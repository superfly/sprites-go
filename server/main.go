package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"lib/api"
	"log/slog"
	"os"
	"os/signal"
	"path/filepath"
	serverapi "spritectl/api"
	"spritectl/api/handlers"
	"sync"
	"syscall"
	"time"

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

	// Overlay configuration
	OverlayEnabled       bool   // Enable root overlay mounting
	OverlayImageSize     string // Size of the overlay image (e.g., "100G")
	OverlayLowerPath     string // Path to lower directory (read-only base layer)
	OverlayTargetPath    string // Where to mount the final overlay
	OverlaySkipOverlayFS bool   // Skip overlayfs, only mount loopback
}

// Application represents the main application
type Application struct {
	config     Config
	logger     *slog.Logger
	juicefs    *juicefs.JuiceFS
	supervisor *supervisor.Supervisor
	apiServer  *serverapi.Server
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

	// Reap event tracking
	reapEventsMu  sync.RWMutex
	reapEvents    map[int]time.Time // Map of PID to reap time
	reapListeners []chan int        // Channels listening for reap events
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
		reapEvents:    make(map[int]time.Time),
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
			// Overlay configuration
			OverlayEnabled:       config.OverlayEnabled,
			OverlayImageSize:     config.OverlayImageSize,
			OverlayLowerPath:     config.OverlayLowerPath,
			OverlayTargetPath:    config.OverlayTargetPath,
			OverlaySkipOverlayFS: config.OverlaySkipOverlayFS,
		}

		jfs, err := juicefs.New(juicefsConfig)
		if err != nil {
			return nil, fmt.Errorf("failed to create JuiceFS instance: %w", err)
		}
		app.juicefs = jfs
	}

	// Set up API server if configured
	if config.APIListenAddr != "" {
		apiConfig := serverapi.Config{
			ListenAddr:            config.APIListenAddr,
			APIToken:              config.APIToken,
			MaxWaitTime:           30 * time.Second,
			ExecWrapperCommand:    config.ExecWrapperCommand,
			ExecTTYWrapperCommand: config.ExecTTYWrapperCommand,
		}

		apiServer, err := serverapi.NewServer(apiConfig, app.commandCh, app, logger)
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

// SubscribeToReapEvents creates a channel that receives PIDs when processes are reaped
func (app *Application) SubscribeToReapEvents() <-chan int {
	app.reapEventsMu.Lock()
	defer app.reapEventsMu.Unlock()

	ch := make(chan int, 10)
	app.reapListeners = append(app.reapListeners, ch)
	return ch
}

// UnsubscribeFromReapEvents removes a reap event listener
func (app *Application) UnsubscribeFromReapEvents(ch <-chan int) {
	app.reapEventsMu.Lock()
	defer app.reapEventsMu.Unlock()

	for i, listener := range app.reapListeners {
		if listener == ch {
			// Remove the listener and close it
			close(listener)
			app.reapListeners = append(app.reapListeners[:i], app.reapListeners[i+1:]...)
			break
		}
	}
}

// WasProcessReaped checks if a process with the given PID was reaped
func (app *Application) WasProcessReaped(pid int) (bool, time.Time) {
	app.reapEventsMu.RLock()
	defer app.reapEventsMu.RUnlock()

	reapTime, found := app.reapEvents[pid]
	return found, reapTime
}

// emitReapEvent notifies all listeners that a process was reaped
func (app *Application) emitReapEvent(pid int) {
	app.reapEventsMu.Lock()
	defer app.reapEventsMu.Unlock()

	// Record the reap event
	app.reapEvents[pid] = time.Now()

	// Clean up old events if map gets too large (keep last 1000)
	if len(app.reapEvents) > 1000 {
		// Find oldest events to remove
		var oldestPIDs []int
		for p := range app.reapEvents {
			oldestPIDs = append(oldestPIDs, p)
			if len(oldestPIDs) > 100 { // Remove 100 oldest
				break
			}
		}
		for _, p := range oldestPIDs {
			delete(app.reapEvents, p)
		}
	}

	// Notify all listeners
	for _, ch := range app.reapListeners {
		select {
		case ch <- pid:
			// Sent successfully
		default:
			// Channel is full, skip
		}
	}
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
			data.StreamCh <- api.StreamMessage{
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

// performRestore handles the restore operation after the supervisor state change
func (app *Application) performRestore(checkpointID string, streamCh chan<- api.StreamMessage) {
	defer close(streamCh)

	app.logger.Info("Starting restore sequence", "checkpointID", checkpointID)
	app.restoringNow = true
	defer func() { app.restoringNow = false }()

	// Track the previous state checkpoint ID
	var previousStateID string

	// Stop process if running
	if app.processRunning && app.supervisor != nil {
		streamCh <- api.StreamMessage{
			Type: "info",
			Data: "Stopping process for restore...",
			Time: time.Now(),
		}
		app.logger.Info("Stopping process for restore")
		if err := app.supervisor.Stop(); err != nil {
			app.logger.Error("Failed to stop process", "error", err)
			streamCh <- api.StreamMessage{
				Type:  "error",
				Error: fmt.Sprintf("Failed to stop process: %v", err),
				Time:  time.Now(),
			}
			return
		}
		// supervisor.Stop() blocks until the process has exited
		app.processRunning = false
		app.logger.Info("Process stopped successfully")
		streamCh <- api.StreamMessage{
			Type: "info",
			Data: "Process stopped successfully",
			Time: time.Now(),
		}
	}

	// Perform JuiceFS restore with streaming
	if app.juicefs != nil {
		streamCh <- api.StreamMessage{
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
			streamCh <- api.StreamMessage{
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
	streamCh <- api.StreamMessage{
		Type: "info",
		Data: "Starting process after restore...",
		Time: time.Now(),
	}
	app.logger.Info("Starting process after restore")
	if err := app.startProcess(); err != nil {
		app.logger.Error("Failed to start process after restore", "error", err)
		streamCh <- api.StreamMessage{
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
	streamCh <- api.StreamMessage{
		Type: "complete",
		Data: completeMessage,
		Time: time.Now(),
	}
}

// streamingCheckpoint performs checkpoint with streaming output
func (app *Application) streamingCheckpoint(ctx context.Context, checkpointID string, streamCh chan<- api.StreamMessage) error {
	if checkpointID == "" {
		return fmt.Errorf("checkpoint ID is required")
	}

	// Send initial message
	streamCh <- api.StreamMessage{
		Type: "info",
		Data: fmt.Sprintf("Creating checkpoint %s...", checkpointID),
		Time: time.Now(),
	}

	// Use the proper JuiceFS checkpoint method that handles overlay
	if err := app.juicefs.Checkpoint(ctx, checkpointID); err != nil {
		streamCh <- api.StreamMessage{
			Type:  "error",
			Error: fmt.Sprintf("Failed to create checkpoint: %v", err),
			Time:  time.Now(),
		}
		return err
	}

	streamCh <- api.StreamMessage{
		Type: "info",
		Data: fmt.Sprintf("Checkpoint created successfully at checkpoints/%s", checkpointID),
		Time: time.Now(),
	}

	// Send final completion message
	streamCh <- api.StreamMessage{
		Type: "complete",
		Data: fmt.Sprintf("Checkpoint %s created successfully", checkpointID),
		Time: time.Now(),
	}

	return nil
}

// streamingRestore performs restore with streaming output
func (app *Application) streamingRestore(ctx context.Context, checkpointID string, streamCh chan<- api.StreamMessage) (string, error) {
	if checkpointID == "" {
		return "", fmt.Errorf("checkpoint ID is required")
	}

	// Send initial message
	streamCh <- api.StreamMessage{
		Type: "info",
		Data: fmt.Sprintf("Restoring from checkpoint %s...", checkpointID),
		Time: time.Now(),
	}

	// Use the proper JuiceFS restore method that handles overlay
	if err := app.juicefs.Restore(ctx, checkpointID); err != nil {
		streamCh <- api.StreamMessage{
			Type:  "error",
			Error: fmt.Sprintf("Failed to restore checkpoint: %v", err),
			Time:  time.Now(),
		}
		return "", err
	}

	// For now, we don't track the previous state ID in the JuiceFS package
	// This would need to be enhanced if we want to return it
	previousStateID := ""

	// Send completion message
	message := fmt.Sprintf("Restore from %s complete", checkpointID)
	if previousStateID != "" {
		message += fmt.Sprintf(", previous state checkpoint id: %s", previousStateID)
	}

	streamCh <- api.StreamMessage{
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

					// Emit reap event
					app.emitReapEvent(pid)
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

			// JuiceFS configuration
			JuiceFSEnabled    bool   `json:"juicefs_enabled"`
			JuiceFSBaseDir    string `json:"juicefs_base_dir"`
			JuiceFSLocalMode  bool   `json:"juicefs_local_mode"`
			JuiceFSVolumeName string `json:"juicefs_volume_name"`
			S3AccessKey       string `json:"s3_access_key"`
			S3SecretAccessKey string `json:"s3_secret_access_key"`
			S3EndpointURL     string `json:"s3_endpoint_url"`
			S3Bucket          string `json:"s3_bucket"`

			// Overlay configuration
			OverlayEnabled       bool   `json:"overlay_enabled"`
			OverlayImageSize     string `json:"overlay_image_size"`
			OverlayLowerPath     string `json:"overlay_lower_path"`
			OverlayTargetPath    string `json:"overlay_target_path"`
			OverlaySkipOverlayFS bool   `json:"overlay_skip_overlayfs"`
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
		config.JuiceFSBaseDir = fileConfig.JuiceFSBaseDir
		config.JuiceFSLocalMode = fileConfig.JuiceFSLocalMode
		config.S3AccessKey = fileConfig.S3AccessKey
		config.S3SecretAccessKey = fileConfig.S3SecretAccessKey
		config.S3EndpointURL = fileConfig.S3EndpointURL
		config.S3Bucket = fileConfig.S3Bucket
		config.OverlayEnabled = fileConfig.OverlayEnabled
		config.OverlayImageSize = fileConfig.OverlayImageSize
		config.OverlayLowerPath = fileConfig.OverlayLowerPath
		config.OverlayTargetPath = fileConfig.OverlayTargetPath
		config.OverlaySkipOverlayFS = fileConfig.OverlaySkipOverlayFS
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

	// JuiceFS configuration - environment overrides file config
	juicefsBaseDir := os.Getenv("SPRITE_WRITE_DIR")
	if juicefsBaseDir != "" {
		config.JuiceFSBaseDir = filepath.Join(juicefsBaseDir, "juicefs")
	}
	if juicefsDirFlag != "" {
		config.JuiceFSBaseDir = juicefsDirFlag
	}

	// Check for local mode
	if os.Getenv("SPRITE_LOCAL_MODE") == "true" {
		config.JuiceFSLocalMode = true
	} else if os.Getenv("SPRITE_LOCAL_MODE") == "false" {
		config.JuiceFSLocalMode = false
	}

	// S3 configuration - environment overrides file config
	if s3Key := os.Getenv("SPRITE_S3_ACCESS_KEY"); s3Key != "" {
		config.S3AccessKey = s3Key
	}
	if s3Secret := os.Getenv("SPRITE_S3_SECRET_ACCESS_KEY"); s3Secret != "" {
		config.S3SecretAccessKey = s3Secret
	}
	if s3Endpoint := os.Getenv("SPRITE_S3_ENDPOINT_URL"); s3Endpoint != "" {
		config.S3EndpointURL = s3Endpoint
	}
	if s3Bucket := os.Getenv("SPRITE_S3_BUCKET"); s3Bucket != "" {
		config.S3Bucket = s3Bucket
	}

	// Overlay configuration - environment overrides file config
	if overlayEnabled := os.Getenv("SPRITE_OVERLAY_ENABLED"); overlayEnabled == "true" {
		config.OverlayEnabled = true
	} else if overlayEnabled == "false" {
		config.OverlayEnabled = false
	}
	if overlaySize := os.Getenv("SPRITE_OVERLAY_IMAGE_SIZE"); overlaySize != "" {
		config.OverlayImageSize = overlaySize
	}
	if overlayLowerPath := os.Getenv("SPRITE_OVERLAY_LOWER_PATH"); overlayLowerPath != "" {
		config.OverlayLowerPath = overlayLowerPath
	}
	if overlayTarget := os.Getenv("SPRITE_OVERLAY_TARGET_PATH"); overlayTarget != "" {
		config.OverlayTargetPath = overlayTarget
	}
	if skipOverlayFS := os.Getenv("SPRITE_OVERLAY_SKIP_OVERLAYFS"); skipOverlayFS == "true" {
		config.OverlaySkipOverlayFS = true
	} else if skipOverlayFS == "false" {
		config.OverlaySkipOverlayFS = false
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
