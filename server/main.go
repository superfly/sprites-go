package main

import (
	"bufio"
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"log/slog"
	"os"
	"os/exec"
	"os/signal"
	"path/filepath"
	"sync"
	"syscall"
	"time"

	"spritectl/api"
	"spritectl/api/handlers"

	"github.com/fly-dev-env/sprite-env/server/packages/juicefs"
	"github.com/sprite-env/server/packages/supervisor"
)

// version is set at build time via ldflags
var version = "dev"

// Config holds simplified application configuration
type Config struct {
	// Logging
	LogLevel slog.Level
	LogJSON  bool
	Debug    bool

	// API Server
	APIListenAddr string
	APIToken      string

	// Process
	ProcessCommand                 []string
	ProcessWorkingDir              string
	ProcessEnvironment             []string
	ProcessGracefulShutdownTimeout time.Duration

	// JuiceFS
	JuiceFSBaseDir    string
	JuiceFSLocalMode  bool
	S3AccessKey       string
	S3SecretAccessKey string
	S3EndpointURL     string
	S3Bucket          string

	// Exec
	ExecWrapperCommand    []string
	ExecTTYWrapperCommand []string

	// Debug
	KeepAliveOnError bool // Keep server running when process fails
}

// Application manages the sprite-env components and implements handlers.ProcessManager
type Application struct {
	config     Config
	logger     *slog.Logger
	juicefs    *juicefs.JuiceFS
	supervisor *supervisor.Supervisor
	apiServer  *api.Server
	ctx        context.Context
	cancel     context.CancelFunc

	// Channels for component communication
	commandCh     chan handlers.Command
	processDoneCh chan error
	httpDoneCh    chan error
	signalCh      chan os.Signal

	// State
	processRunning bool
	restoringNow   bool

	// Background task management
	reaperDone chan struct{}
}

// NewApplication creates a new application instance
func NewApplication(config Config) (*Application, error) {
	// Set up logging
	var handler slog.Handler
	if config.LogJSON {
		handler = slog.NewJSONHandler(os.Stdout, &slog.HandlerOptions{
			Level: config.LogLevel,
		})
	} else {
		handler = slog.NewTextHandler(os.Stdout, &slog.HandlerOptions{
			Level: config.LogLevel,
		})
	}
	logger := slog.New(handler)

	ctx, cancel := context.WithCancel(context.Background())

	app := &Application{
		config:        config,
		logger:        logger,
		ctx:           ctx,
		cancel:        cancel,
		commandCh:     make(chan handlers.Command, 10),
		processDoneCh: make(chan error, 1),
		httpDoneCh:    make(chan error, 1),
		signalCh:      make(chan os.Signal, 1),
		reaperDone:    make(chan struct{}),
	}

	// Set up JuiceFS if base directory is configured
	if config.JuiceFSBaseDir != "" {
		juicefsConfig := juicefs.Config{
			BaseDir:           config.JuiceFSBaseDir,
			LocalMode:         config.JuiceFSLocalMode,
			S3AccessKey:       config.S3AccessKey,
			S3SecretAccessKey: config.S3SecretAccessKey,
			S3EndpointURL:     config.S3EndpointURL,
			S3Bucket:          config.S3Bucket,
			VolumeName:        "sprite-juicefs",
		}

		jfs, err := juicefs.New(juicefsConfig)
		if err != nil {
			return nil, fmt.Errorf("failed to create JuiceFS instance: %w", err)
		}
		app.juicefs = jfs
	}

	// Set up API server if configured
	if config.APIListenAddr != "" {
		apiConfig := api.Config{
			ListenAddr:            config.APIListenAddr,
			APIToken:              config.APIToken,
			MaxWaitTime:           30 * time.Second,
			ExecWrapperCommand:    config.ExecWrapperCommand,
			ExecTTYWrapperCommand: config.ExecTTYWrapperCommand,
		}

		apiServer, err := api.NewServer(apiConfig, app.commandCh, app, logger)
		if err != nil {
			return nil, fmt.Errorf("failed to create API server: %w", err)
		}
		app.apiServer = apiServer
	}

	return app, nil
}

// ProcessManager interface implementation

// SendCommand implements handlers.ProcessManager
func (app *Application) SendCommand(cmd handlers.Command) handlers.CommandResponse {
	// This is called by the API server, but we handle commands in the event loop
	// So we just forward the command and wait for response
	select {
	case app.commandCh <- cmd:
		// Command sent successfully
		return handlers.CommandResponse{Success: true}
	case <-time.After(time.Second):
		return handlers.CommandResponse{
			Success: false,
			Error:   fmt.Errorf("timeout sending command"),
		}
	}
}

// IsProcessRunning implements handlers.ProcessManager
func (app *Application) IsProcessRunning() bool {
	return app.processRunning
}

// Start starts the application components
func (app *Application) Start(ctx context.Context) error {
	app.logger.Info("Starting sprite-env application", "version", version)

	// Log debug settings
	if app.config.KeepAliveOnError {
		app.logger.Info("Keep-alive mode enabled - server will continue running if process fails")
	}

	// Start zombie reaper if running as PID 1
	app.startReaper()

	// Start JuiceFS if configured
	if app.juicefs != nil {
		app.logger.Info("Starting JuiceFS...")
		if err := app.juicefs.Start(ctx); err != nil {
			return fmt.Errorf("failed to start JuiceFS: %w", err)
		}
		app.logger.Info("JuiceFS started successfully")
	}

	// Start API server if configured
	if app.apiServer != nil {
		go func() {
			err := app.apiServer.Start()
			if err != nil {
				app.httpDoneCh <- err
			}
		}()
	}

	// Start supervised process
	if len(app.config.ProcessCommand) > 0 {
		app.logger.Info("Starting supervised process...")
		if err := app.startProcess(); err != nil {
			// If process fails to start, stop JuiceFS
			if app.juicefs != nil {
				stopCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
				defer cancel()
				app.juicefs.Stop(stopCtx)
			}
			return fmt.Errorf("failed to start process: %w", err)
		}
	}

	// Set up signal handling
	signal.Notify(app.signalCh, syscall.SIGTERM, syscall.SIGINT, syscall.SIGHUP)
	// Note: SIGCHLD is handled separately by startReaper() when running as PID 1

	// Start the main event loop
	go app.eventLoop()

	app.logger.Info("Application started successfully")
	return nil
}

// startProcess starts the supervised process
func (app *Application) startProcess() error {
	if len(app.config.ProcessCommand) == 0 {
		return fmt.Errorf("no process command configured")
	}

	// Set up process working directory
	workingDir := app.config.ProcessWorkingDir
	if app.juicefs != nil && workingDir == "" {
		// Default to JuiceFS active directory if available
		workingDir = filepath.Join(app.config.JuiceFSBaseDir, "data", "active", "fs")
	}

	supervisorConfig := supervisor.Config{
		Command:     app.config.ProcessCommand[0],
		Args:        app.config.ProcessCommand[1:],
		GracePeriod: app.config.ProcessGracefulShutdownTimeout,
		Env:         append(os.Environ(), app.config.ProcessEnvironment...),
		Dir:         workingDir,
	}

	sup, err := supervisor.New(supervisorConfig)
	if err != nil {
		return fmt.Errorf("failed to create supervisor: %w", err)
	}

	pid, err := sup.Start()
	if err != nil {
		return fmt.Errorf("failed to start process: %w", err)
	}

	app.supervisor = sup
	app.processRunning = true

	app.logger.Info("Process started", "pid", pid, "command", app.config.ProcessCommand)

	// Monitor process in background
	go func() {
		err := app.supervisor.Wait()
		app.processDoneCh <- err
	}()

	return nil
}

// eventLoop is the main event loop that monitors all components
func (app *Application) eventLoop() {
	for {
		select {
		case err := <-app.processDoneCh:
			// Process exited
			app.processRunning = false

			if err != nil {
				app.logger.Error("Process exited with error", "error", err)
			} else {
				app.logger.Info("Process exited normally")
			}

			// If not restoring and process exited on its own, stop JuiceFS and exit
			if !app.restoringNow {
				if app.config.KeepAliveOnError {
					app.logger.Info("Process exited, but keeping server alive (SPRITE_KEEP_ALIVE_ON_ERROR=true)")
					app.logger.Info("Server is still running and accepting API requests")
					// Continue the event loop instead of shutting down
				} else {
					app.logger.Info("Process exited, stopping application...")
					app.shutdown(0)
					return
				}
			}

		case err := <-app.httpDoneCh:
			// HTTP server stopped
			if err != nil {
				app.logger.Error("HTTP server error", "error", err)
			}
			app.shutdown(1)
			return

		case sig := <-app.signalCh:
			switch sig {
			case syscall.SIGTERM, syscall.SIGINT:
				app.logger.Info("Received shutdown signal", "signal", sig)
				exitCode := 0
				if sig == syscall.SIGTERM {
					exitCode = 143 // 128 + 15
				} else if sig == syscall.SIGINT {
					exitCode = 130 // 128 + 2
				}
				app.shutdown(exitCode)
				return

			default:
				// Forward other signals to process
				if app.processRunning && app.supervisor != nil {
					if err := app.supervisor.Signal(sig); err != nil {
						app.logger.Warn("Failed to forward signal", "signal", sig, "error", err)
					}
				}
			}

		case cmd := <-app.commandCh:
			// Handle commands from API server
			app.handleCommand(cmd)
		}
	}
}

// handleCommand processes commands from the API server
func (app *Application) handleCommand(cmd handlers.Command) {
	switch cmd.Type {
	case handlers.CommandGetStatus:
		cmd.Response <- handlers.CommandResponse{
			Success: true,
			Data:    app.processRunning,
		}

	case handlers.CommandCheckpoint:
		data := cmd.Data.(handlers.CheckpointData)
		if app.juicefs != nil {
			go func() {
				defer close(data.StreamCh)

				ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
				defer cancel()

				// Stream the checkpoint operation
				err := app.streamingCheckpoint(ctx, data.CheckpointID, data.StreamCh)

				cmd.Response <- handlers.CommandResponse{
					Success: err == nil,
					Error:   err,
				}
			}()
		} else {
			// Send error message before closing channel
			data.StreamCh <- handlers.StreamMessage{
				Type:  "error",
				Error: "JuiceFS not configured",
				Time:  time.Now(),
			}
			close(data.StreamCh)
			cmd.Response <- handlers.CommandResponse{
				Success: false,
				Error:   fmt.Errorf("JuiceFS not configured"),
			}
		}

	case handlers.CommandRestore:
		data := cmd.Data.(handlers.RestoreData)
		// Start restore process asynchronously with streaming
		go app.performRestore(data.CheckpointID, data.StreamCh)

		// Immediately respond that restore was initiated
		cmd.Response <- handlers.CommandResponse{
			Success: true,
		}
	}
}

// performRestore performs the restore sequence with streaming progress
func (app *Application) performRestore(checkpointID string, streamCh chan<- handlers.StreamMessage) {
	defer close(streamCh)

	app.logger.Info("Starting restore sequence", "checkpointID", checkpointID)
	app.restoringNow = true
	defer func() { app.restoringNow = false }()

	// Track the previous state checkpoint ID
	var previousStateID string

	// Stop process if running
	if app.processRunning && app.supervisor != nil {
		streamCh <- handlers.StreamMessage{
			Type: "info",
			Data: "Stopping process for restore...",
			Time: time.Now(),
		}
		app.logger.Info("Stopping process for restore")
		if err := app.supervisor.Stop(); err != nil {
			app.logger.Error("Failed to stop process", "error", err)
			streamCh <- handlers.StreamMessage{
				Type:  "error",
				Error: fmt.Sprintf("Failed to stop process: %v", err),
				Time:  time.Now(),
			}
			return
		}
		// supervisor.Stop() blocks until the process has exited
		app.processRunning = false
		app.logger.Info("Process stopped successfully")
		streamCh <- handlers.StreamMessage{
			Type: "info",
			Data: "Process stopped successfully",
			Time: time.Now(),
		}
	}

	// Perform JuiceFS restore with streaming
	if app.juicefs != nil {
		streamCh <- handlers.StreamMessage{
			Type: "info",
			Data: fmt.Sprintf("Restoring from checkpoint %s...", checkpointID),
			Time: time.Now(),
		}
		app.logger.Info("Restoring from checkpoint", "checkpointID", checkpointID)
		ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
		defer cancel()

		previousStateID, err := app.streamingRestore(ctx, checkpointID, streamCh)
		if err != nil {
			app.logger.Error("Failed to restore checkpoint", "error", err)
			streamCh <- handlers.StreamMessage{
				Type:  "error",
				Error: fmt.Sprintf("Failed to restore checkpoint: %v", err),
				Time:  time.Now(),
			}
			return
		}
		app.logger.Info("Checkpoint restored successfully", "previousStateID", previousStateID)
		// Don't send a message here - streamingRestore already sent the completion message
	}

	// Restart process
	streamCh <- handlers.StreamMessage{
		Type: "info",
		Data: "Starting process after restore...",
		Time: time.Now(),
	}
	app.logger.Info("Starting process after restore")
	if err := app.startProcess(); err != nil {
		app.logger.Error("Failed to start process after restore", "error", err)
		streamCh <- handlers.StreamMessage{
			Type:  "error",
			Error: fmt.Sprintf("Failed to start process after restore: %v", err),
			Time:  time.Now(),
		}
		return
	}

	app.logger.Info("Restore sequence completed")
	// Update the final message to include the previous state info if available
	completeMessage := fmt.Sprintf("Restore from %s complete", checkpointID)
	if previousStateID != "" {
		completeMessage += fmt.Sprintf(", previous state checkpoint id: %s", previousStateID)
	}
	streamCh <- handlers.StreamMessage{
		Type: "complete",
		Data: completeMessage,
		Time: time.Now(),
	}
}

// streamingCheckpoint performs checkpoint with streaming output
func (app *Application) streamingCheckpoint(ctx context.Context, checkpointID string, streamCh chan<- handlers.StreamMessage) error {
	if checkpointID == "" {
		return fmt.Errorf("checkpoint ID is required")
	}

	mountPath := filepath.Join(app.config.JuiceFSBaseDir, "data")
	activeDir := filepath.Join(mountPath, "active")
	checkpointsDir := filepath.Join(mountPath, "checkpoints")
	checkpointPath := filepath.Join(checkpointsDir, checkpointID)

	// Ensure checkpoints directory exists
	if err := os.MkdirAll(checkpointsDir, 0755); err != nil {
		return fmt.Errorf("failed to create checkpoints directory: %w", err)
	}

	// Check if active directory exists
	if _, err := os.Stat(activeDir); os.IsNotExist(err) {
		return fmt.Errorf("active directory does not exist at %s", activeDir)
	}

	// Check if checkpoint already exists
	if _, err := os.Stat(checkpointPath); err == nil {
		return fmt.Errorf("checkpoint %s already exists at %s", checkpointID, checkpointPath)
	}

	// Send initial message
	streamCh <- handlers.StreamMessage{
		Type: "info",
		Data: fmt.Sprintf("Creating checkpoint %s...", checkpointID),
		Time: time.Now(),
	}

	// Create and run the juicefs clone command
	cmd := exec.CommandContext(ctx, "juicefs", "clone", activeDir, checkpointPath)

	// Capture stdout and stderr
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		return fmt.Errorf("failed to create stdout pipe: %w", err)
	}

	stderr, err := cmd.StderrPipe()
	if err != nil {
		return fmt.Errorf("failed to create stderr pipe: %w", err)
	}

	// Start the command
	if err := cmd.Start(); err != nil {
		return fmt.Errorf("failed to start juicefs clone: %w", err)
	}

	// Stream output
	var wg sync.WaitGroup
	wg.Add(2)

	// Stream stdout
	go func() {
		defer wg.Done()
		scanner := bufio.NewScanner(stdout)
		for scanner.Scan() {
			streamCh <- handlers.StreamMessage{
				Type: "stdout",
				Data: scanner.Text(),
				Time: time.Now(),
			}
		}
	}()

	// Stream stderr
	go func() {
		defer wg.Done()
		scanner := bufio.NewScanner(stderr)
		for scanner.Scan() {
			streamCh <- handlers.StreamMessage{
				Type: "stderr",
				Data: scanner.Text(),
				Time: time.Now(),
			}
		}
	}()

	// Wait for command to complete
	wg.Wait()
	err = cmd.Wait()

	if err != nil {
		streamCh <- handlers.StreamMessage{
			Type:  "error",
			Error: fmt.Sprintf("juicefs clone failed: %v", err),
			Time:  time.Now(),
		}
		return fmt.Errorf("juicefs clone failed: %w", err)
	}

	streamCh <- handlers.StreamMessage{
		Type: "info",
		Data: fmt.Sprintf("Checkpoint created successfully at %s", checkpointPath),
		Time: time.Now(),
	}

	// Send final completion message
	streamCh <- handlers.StreamMessage{
		Type: "complete",
		Data: fmt.Sprintf("Checkpoint %s created successfully", checkpointID),
		Time: time.Now(),
	}

	return nil
}

// streamingRestore performs restore with streaming output
func (app *Application) streamingRestore(ctx context.Context, checkpointID string, streamCh chan<- handlers.StreamMessage) (string, error) {
	if checkpointID == "" {
		return "", fmt.Errorf("checkpoint ID is required")
	}

	mountPath := filepath.Join(app.config.JuiceFSBaseDir, "data")
	activeDir := filepath.Join(mountPath, "active")
	checkpointsDir := filepath.Join(mountPath, "checkpoints")
	checkpointPath := filepath.Join(checkpointsDir, checkpointID)

	// Check if checkpoint exists
	if _, err := os.Stat(checkpointPath); os.IsNotExist(err) {
		return "", fmt.Errorf("checkpoint %s does not exist at %s", checkpointID, checkpointPath)
	}

	// Track the backup name for the previous state
	var previousStateID string

	// If active directory exists, back it up
	if _, err := os.Stat(activeDir); err == nil {
		timestamp := time.Now().Unix()
		backupName := fmt.Sprintf("pre-restore-%s-%d", checkpointID, timestamp)
		backupPath := filepath.Join(checkpointsDir, backupName)
		previousStateID = backupName

		streamCh <- handlers.StreamMessage{
			Type: "info",
			Data: fmt.Sprintf("Backing up current active directory to %s...", backupName),
			Time: time.Now(),
		}

		if err := os.Rename(activeDir, backupPath); err != nil {
			return "", fmt.Errorf("failed to backup active directory: %w", err)
		}

		streamCh <- handlers.StreamMessage{
			Type: "info",
			Data: "Backup completed",
			Time: time.Now(),
		}
	}

	// Clone checkpoint to active directory
	streamCh <- handlers.StreamMessage{
		Type: "info",
		Data: fmt.Sprintf("Cloning checkpoint %s to active directory...", checkpointID),
		Time: time.Now(),
	}

	cmd := exec.CommandContext(ctx, "juicefs", "clone", checkpointPath, activeDir)

	// Capture stdout and stderr
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		return "", fmt.Errorf("failed to create stdout pipe: %w", err)
	}

	stderr, err := cmd.StderrPipe()
	if err != nil {
		return "", fmt.Errorf("failed to create stderr pipe: %w", err)
	}

	// Start the command
	if err := cmd.Start(); err != nil {
		return "", fmt.Errorf("failed to start juicefs clone: %w", err)
	}

	// Stream output
	var wg sync.WaitGroup
	wg.Add(2)

	// Stream stdout
	go func() {
		defer wg.Done()
		scanner := bufio.NewScanner(stdout)
		for scanner.Scan() {
			streamCh <- handlers.StreamMessage{
				Type: "stdout",
				Data: scanner.Text(),
				Time: time.Now(),
			}
		}
	}()

	// Stream stderr
	go func() {
		defer wg.Done()
		scanner := bufio.NewScanner(stderr)
		for scanner.Scan() {
			streamCh <- handlers.StreamMessage{
				Type: "stderr",
				Data: scanner.Text(),
				Time: time.Now(),
			}
		}
	}()

	// Wait for command to complete
	wg.Wait()
	err = cmd.Wait()

	if err != nil {
		return "", fmt.Errorf("juicefs clone failed: %w", err)
	}

	// Send completion message with the format requested by the user
	message := fmt.Sprintf("Restore from %s complete", checkpointID)
	if previousStateID != "" {
		message += fmt.Sprintf(", previous state checkpoint id: %s", previousStateID)
	}

	streamCh <- handlers.StreamMessage{
		Type: "info",
		Data: message,
		Time: time.Now(),
	}

	return previousStateID, nil
}

// shutdown performs graceful shutdown
func (app *Application) shutdown(exitCode int) {
	app.logger.Info("Shutting down application")

	// Cancel context to signal shutdown
	app.cancel()

	// Stop API server
	if app.apiServer != nil {
		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		if err := app.apiServer.Stop(ctx); err != nil {
			app.logger.Error("Failed to stop API server", "error", err)
		}
		cancel()
	}

	// Stop supervised process
	if app.processRunning && app.supervisor != nil {
		app.logger.Info("Stopping supervised process...")
		if err := app.supervisor.Stop(); err != nil {
			app.logger.Error("Failed to stop process", "error", err)
		}
	}

	// Stop JuiceFS
	if app.juicefs != nil {
		app.logger.Info("Stopping JuiceFS...")
		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		if err := app.juicefs.Stop(ctx); err != nil {
			app.logger.Error("Failed to stop JuiceFS", "error", err)
		}
		cancel()
	}

	// Wait for zombie reaper to finish with a timeout
	select {
	case <-app.reaperDone:
		app.logger.Debug("Zombie reaper stopped cleanly")
	case <-time.After(1 * time.Second):
		app.logger.Warn("Zombie reaper did not stop within timeout")
	}

	app.logger.Info("Application stopped", "exitCode", exitCode)
	os.Exit(exitCode)
}

// startReaper starts a goroutine to reap zombie processes when running as PID 1
//
// Safety guarantees:
// - syscall.Wait4 uses WNOHANG flag, so it never blocks
// - The goroutine listens for context cancellation and exits cleanly
// - Signal handler is properly cleaned up with signal.Stop()
// - The shutdown() function waits (with timeout) for this goroutine to finish
func (app *Application) startReaper() {
	// Only start reaper if we're PID 1
	if os.Getpid() != 1 {
		close(app.reaperDone) // Signal immediately that reaper is "done" since it never started
		return
	}

	app.logger.Info("Running as PID 1, starting zombie reaper")

	// Create a separate signal channel for SIGCHLD
	sigchldCh := make(chan os.Signal, 10)
	signal.Notify(sigchldCh, syscall.SIGCHLD)

	go func() {
		defer close(app.reaperDone)
		defer signal.Stop(sigchldCh)

		for {
			select {
			case <-app.ctx.Done():
				return
			case <-sigchldCh:
				// Reap all available zombie processes
				for {
					var status syscall.WaitStatus
					pid, err := syscall.Wait4(-1, &status, syscall.WNOHANG, nil)
					if err != nil {
						// ECHILD is expected when there are no child processes
						if err != syscall.ECHILD {
							app.logger.Debug("Error during wait4", "error", err)
						}
						break
					}
					if pid <= 0 {
						// No more zombies to reap
						break
					}
					app.logger.Debug("Reaped zombie process", "pid", pid, "status", status)
				}
			}
		}
	}()
}

// Command-line parsing and main

func parseCommandLine() (Config, error) {
	var config Config

	// Flags
	var (
		configFile              string
		debug                   bool
		logJSON                 bool
		listenAddr              string
		gracefulShutdownTimeout time.Duration
		juicefsDirFlag          string
		showVersion             bool
	)

	flag.StringVar(&configFile, "config", "", "JSON configuration file")
	flag.BoolVar(&debug, "debug", false, "Enable debug logging")
	flag.BoolVar(&logJSON, "log-json", false, "Output logs in JSON format")
	flag.StringVar(&listenAddr, "listen", "", "API server listen address")
	flag.DurationVar(&gracefulShutdownTimeout, "graceful-shutdown-timeout", 30*time.Second, "Process graceful shutdown timeout")
	flag.StringVar(&juicefsDirFlag, "juicefs-dir", "", "JuiceFS base directory")
	flag.BoolVar(&showVersion, "version", false, "Show version and exit")
	flag.Parse()

	if showVersion {
		fmt.Printf("sprite-env version %s\n", version)
		os.Exit(0)
	}

	// Load from config file if specified
	if configFile != "" {
		data, err := os.ReadFile(configFile)
		if err != nil {
			return config, fmt.Errorf("failed to read config file: %w", err)
		}

		var fileConfig struct {
			LogLevel              string   `json:"log_level"`
			LogJSON               bool     `json:"log_json"`
			APIListen             string   `json:"api_listen_addr"`
			ProcessCmd            []string `json:"process_command"`
			ProcessDir            string   `json:"process_working_dir"`
			ProcessEnv            []string `json:"process_environment"`
			ExecWrapperCommand    []string `json:"exec_wrapper_command"`
			ExecTTYWrapperCommand []string `json:"exec_tty_wrapper_command"`
		}

		if err := json.Unmarshal(data, &fileConfig); err != nil {
			return config, fmt.Errorf("failed to parse config file: %w", err)
		}

		// Apply file config
		if fileConfig.LogLevel != "" {
			switch fileConfig.LogLevel {
			case "debug":
				config.LogLevel = slog.LevelDebug
			case "info":
				config.LogLevel = slog.LevelInfo
			case "warn":
				config.LogLevel = slog.LevelWarn
			case "error":
				config.LogLevel = slog.LevelError
			}
		}
		config.LogJSON = fileConfig.LogJSON
		config.APIListenAddr = fileConfig.APIListen
		config.ProcessCommand = fileConfig.ProcessCmd
		config.ProcessWorkingDir = fileConfig.ProcessDir
		config.ProcessEnvironment = fileConfig.ProcessEnv
		config.ExecWrapperCommand = fileConfig.ExecWrapperCommand
		config.ExecTTYWrapperCommand = fileConfig.ExecTTYWrapperCommand
	}

	// Apply command-line overrides
	if debug {
		config.Debug = true
		config.LogLevel = slog.LevelDebug
	}
	if logJSON {
		config.LogJSON = true
	}
	if listenAddr != "" {
		config.APIListenAddr = listenAddr
	}
	config.ProcessGracefulShutdownTimeout = gracefulShutdownTimeout

	// Get process command from remaining args
	args := flag.Args()
	if len(args) > 0 {
		config.ProcessCommand = args
	}

	// Environment variables
	config.APIToken = os.Getenv("SPRITE_HTTP_API_TOKEN")

	// JuiceFS configuration
	config.JuiceFSBaseDir = os.Getenv("SPRITE_WRITE_DIR")
	if config.JuiceFSBaseDir != "" {
		config.JuiceFSBaseDir = filepath.Join(config.JuiceFSBaseDir, "juicefs")
	}
	if juicefsDirFlag != "" {
		config.JuiceFSBaseDir = juicefsDirFlag
	}

	// Check for local mode
	if os.Getenv("SPRITE_LOCAL_MODE") == "true" {
		config.JuiceFSLocalMode = true
	} else {
		// S3 configuration
		config.S3AccessKey = os.Getenv("SPRITE_S3_ACCESS_KEY")
		config.S3SecretAccessKey = os.Getenv("SPRITE_S3_SECRET_ACCESS_KEY")
		config.S3EndpointURL = os.Getenv("SPRITE_S3_ENDPOINT_URL")
		config.S3Bucket = os.Getenv("SPRITE_S3_BUCKET")
	}

	// Debug configuration
	if os.Getenv("SPRITE_KEEP_ALIVE_ON_ERROR") == "true" {
		config.KeepAliveOnError = true
	}

	// Validate - now API token is required if API server is configured
	if config.APIListenAddr != "" && config.APIToken == "" {
		return config, fmt.Errorf("API token must be set when API server is enabled")
	}

	return config, nil
}

func main() {
	config, err := parseCommandLine()
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		flag.Usage()
		os.Exit(1)
	}

	app, err := NewApplication(config)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Failed to create application: %v\n", err)
		os.Exit(1)
	}

	// Start application
	ctx := context.Background()
	if err := app.Start(ctx); err != nil {
		app.logger.Error("Failed to start application", "error", err)
		os.Exit(1)
	}

	// Block forever - the event loop handles everything
	select {}
}
