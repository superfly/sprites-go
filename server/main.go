package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"log/slog"
	"os"
	"os/exec"
	"os/signal"
	"path/filepath"
	"runtime/debug"
	"strings"
	"syscall"
	"time"

	"github.com/superfly/sprite-env/pkg/services"
	"github.com/superfly/sprite-env/pkg/tap"
	"github.com/superfly/sprite-env/pkg/terminal"
	serverapi "github.com/superfly/sprite-env/server/api"
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
	AdminToken    string // Optional admin-specific token

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
	ExecWrapperCommand []string

	// Debug
	KeepAliveOnError bool // Keep server running when process fails

	// Overlay configuration
	OverlayEnabled       bool     // Enable root overlay mounting
	OverlayImageSize     string   // Size of the overlay image (e.g., "100G")
	OverlayLowerPath     string   // Path to lower directory (read-only base layer) - deprecated, use OverlayLowerPaths
	OverlayLowerPaths    []string // Paths to lower directories (read-only base layers) - preferred over OverlayLowerPath
	OverlayTargetPath    string   // Where to mount the final overlay
	OverlaySkipOverlayFS bool     // Skip overlayfs, only mount loopback

	// Proxy configuration
	ProxyLocalhostIPv4 string // IPv4 address to use when proxying to localhost
	ProxyLocalhostIPv6 string // IPv6 address to use when proxying to localhost
}

// GetOverlayLowerPaths returns the overlay lower paths with priority and fallback logic
func (c *Config) GetOverlayLowerPaths() []string {
	// Prioritize array format
	if len(c.OverlayLowerPaths) > 0 {
		return c.OverlayLowerPaths
	}

	// Fall back to single string format
	if c.OverlayLowerPath != "" {
		return []string{c.OverlayLowerPath}
	}

	// Default fallback
	return []string{"/mnt/system-base"}
}

// Application represents the main application
type Application struct {
	config           Config
	logger           *slog.Logger
	ctx              context.Context
	cancel           context.CancelFunc
	system           *System
	apiServer        *serverapi.Server
	sockServer       *SockServer
	servicesManager  *services.Manager
	keepAliveOnError bool
	reaper           *Reaper
	resourceMonitor  *ResourceMonitor
	adminChannel     *AdminChannel
}

// NewApplication creates a new application instance
func NewApplication(config Config) (*Application, error) {
	// Set up logging using tap logger
	logger := tap.NewLogger(config.LogLevel, config.LogJSON, os.Stdout)
	tap.SetDefault(logger)

	// Create context with logger
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	ctx, cancel := context.WithCancel(ctx)

	app := &Application{
		config:           config,
		logger:           tap.Logger(ctx),
		ctx:              ctx,
		cancel:           cancel,
		keepAliveOnError: config.KeepAliveOnError,
	}

	// Create Reaper instance
	app.reaper = NewReaper(ctx)

	// Initialize resource monitor (linux only implementation)
	app.resourceMonitor = NewResourceMonitor(ctx)

	// Initialize admin channel (if configured)
	app.adminChannel = NewAdminChannel(ctx)

	// Require SPRITE_WRITE_DIR to be set
	writeDir := os.Getenv("SPRITE_WRITE_DIR")
	if writeDir == "" {
		return nil, fmt.Errorf("SPRITE_WRITE_DIR environment variable is not set")
	}

	// Create services manager with logging
	servicesDataPath := "/mnt/user-data"
	logDir := filepath.Join(writeDir, "logs")
	servicesManager, err := services.NewManager(servicesDataPath, services.WithLogDir(logDir))
	if err != nil {
		return nil, fmt.Errorf("failed to create services manager: %w", err)
	}
	// Set the command prefix for executing services in the container
	if len(config.ExecWrapperCommand) > 0 {
		servicesManager.SetCmdPrefix(config.ExecWrapperCommand)
	}
	app.servicesManager = servicesManager

	// Create System instance
	systemConfig := SystemConfig{
		ProcessCommand:                 config.ProcessCommand,
		ProcessWorkingDir:              config.ProcessWorkingDir,
		ProcessEnvironment:             config.ProcessEnvironment,
		ProcessGracefulShutdownTimeout: config.ProcessGracefulShutdownTimeout,
		JuiceFSBaseDir:                 config.JuiceFSBaseDir,
		JuiceFSLocalMode:               config.JuiceFSLocalMode,
		S3AccessKey:                    config.S3AccessKey,
		S3SecretAccessKey:              config.S3SecretAccessKey,
		S3EndpointURL:                  config.S3EndpointURL,
		S3Bucket:                       config.S3Bucket,
		OverlayEnabled:                 config.OverlayEnabled,
		OverlayImageSize:               config.OverlayImageSize,
		OverlayLowerPath:               config.OverlayLowerPath,
		OverlayLowerPaths:              config.GetOverlayLowerPaths(),
		OverlayTargetPath:              config.OverlayTargetPath,
		OverlaySkipOverlayFS:           config.OverlaySkipOverlayFS,
	}

	system, err := NewSystem(systemConfig, tap.Logger(ctx), app.reaper, app.adminChannel, servicesManager)
	if err != nil {
		return nil, fmt.Errorf("failed to create system: %w", err)
	}

	app.system = system

	// Set up services socket server
	sockServer, err := NewSockServer(ctx, system, logDir)
	if err != nil {
		return nil, fmt.Errorf("failed to create socket server: %w", err)
	}
	app.sockServer = sockServer

	// Set up API server if configured
	if config.APIListenAddr != "" {
		// Calculate the sync target path
		var syncTargetPath string
		if config.JuiceFSBaseDir != "" {
			syncTargetPath = filepath.Join(config.JuiceFSBaseDir, "mount", "active", "fs")
		} else {
			// Fallback to /tmp/sync if JuiceFS is not configured
			syncTargetPath = "/tmp/sync"
		}

		// Create TMUXManager for terminal management
		tmuxManager := terminal.NewTMUXManager(ctx)
		// Set the command prefix for executing tmux in the container
		if len(config.ExecWrapperCommand) > 0 {
			tmuxManager.SetCmdPrefix(config.ExecWrapperCommand)
		}

		apiConfig := serverapi.Config{
			ListenAddr:         config.APIListenAddr,
			APIToken:           config.APIToken,
			AdminToken:         config.AdminToken,
			MaxWaitTime:        30 * time.Second,
			ExecWrapperCommand: config.ExecWrapperCommand,
			SyncTargetPath:     syncTargetPath,
			ProxyLocalhostIPv4: config.ProxyLocalhostIPv4,
			ProxyLocalhostIPv6: config.ProxyLocalhostIPv6,
			TMUXManager:        tmuxManager,
		}

		apiServer, err := serverapi.NewServer(apiConfig, app.system, ctx)
		if err != nil {
			return nil, fmt.Errorf("failed to create API server: %w", err)
		}

		// Start activity monitor and connect to API server
		activity := NewActivityMonitor(ctx, app.system, 30*time.Second)
		activity.SetAdminChannel(app.adminChannel)
		apiServer.SetActivityObserver(func(start bool) {
			if start {
				activity.ActivityStarted("http")
			} else {
				activity.ActivityEnded("http")
			}
		})
		activity.Start(ctx)

		// Set up prepare command for tmux monitoring
		if tmuxManager != nil {
			logger.Info("Setting up tmux activity monitor prepare command")
			tmuxManager.SetPrepareCommand(func() {
				// Start the tmux activity monitor
				logger.Info("Prepare command executing - starting tmux activity monitor",
					"tmuxManagerNil", tmuxManager == nil)

				if tmuxManager == nil {
					logger.Error("TMUXManager is nil in prepare command")
					return
				}

				defer func() {
					if r := recover(); r != nil {
						logger.Error("Panic in tmux activity monitor startup",
							"panic", r,
							"stack", string(debug.Stack()))
					}
				}()

				if err := tmuxManager.StartActivityMonitor(ctx); err != nil {
					logger.Warn("Failed to start tmux activity monitor", "error", err)
				} else {
					logger.Info("Successfully started tmux activity monitor")
				}
			})

			// Connect tmux activity events to the activity monitor
			go func() {
				logger.Info("Starting tmux activity event forwarder")
				activityChan := tmuxManager.GetActivityChannel()
				for {
					select {
					case <-ctx.Done():
						logger.Debug("Tmux activity forwarder stopped due to context cancellation")
						return
					case tmuxActivity, ok := <-activityChan:
						if !ok {
							logger.Error("Tmux activity channel closed unexpectedly")
							return
						}

						logger.Debug("Received tmux activity event",
							"sessionID", tmuxActivity.SessionID,
							"active", tmuxActivity.Active,
							"type", tmuxActivity.Type)

						// Forward to activity monitor
						if tmuxActivity.Active {
							activity.ActivityStarted("tmux")
						} else {
							activity.ActivityEnded("tmux")
						}
					}
				}
			}()
		} else {
			logger.Warn("TMUXManager is nil, cannot set up activity monitor")
		}
		// Pass admin channel to API server for context enrichment
		if app.adminChannel != nil {
			apiServer.SetAdminChannel(app.adminChannel)
		}
		app.apiServer = apiServer
	}

	return app, nil
}

// Run starts and runs the application
func (app *Application) Run() error {
	app.logger.Debug("Starting sprite-env application", "version", version)

	// Log debug settings
	if app.config.KeepAliveOnError {
		app.logger.Debug("Keep-alive mode enabled - server will continue running if process fails")
	}

	// Start zombie reaper
	app.reaper.Start()

	// Start admin channel if configured
	if app.adminChannel != nil {
		app.logger.Info("Starting admin channel")
		if err := app.adminChannel.Start(); err != nil {
			app.logger.Error("Failed to start admin channel", "error", err)
			// Non-fatal, continue without admin channel
		} else {
			app.logger.Info("Admin channel started successfully")
		}
	} else {
		app.logger.Info("Admin channel is not configured (nil)")
	}

	// Start API server if configured - moved before system boot to start listening early
	if app.apiServer != nil {
		go func() {
			if err := app.apiServer.Start(); err != nil {
				app.logger.Error("API server error", "error", err)
				// Trigger shutdown if API server fails
				app.cancel()
			}
		}()
	}

	// Start socket server for services API
	if app.sockServer != nil {
		socketPath := "/tmp/sprite.sock"
		if err := app.sockServer.Start(socketPath); err != nil {
			app.logger.Error("Failed to start socket server", "error", err)
			// Non-fatal, services API will not be available
		} else {
			app.logger.Info("Socket server started", "path", socketPath)
		}
	}

	// Wait for boot signal if configured - moved after HTTP server starts
	if os.Getenv("WAIT_FOR_BOOT") == "true" {
		app.logger.Info("WAIT_FOR_BOOT enabled, HTTP server is listening, waiting for SIGUSR1...")
		sigCh := make(chan os.Signal, 1)
		signal.Notify(sigCh, syscall.SIGUSR1)
		<-sigCh
		signal.Stop(sigCh) // Stop receiving on this channel
		app.logger.Info("Received SIGUSR1, continuing boot...")
	}

	// Setup /dev/fly_vol mount if not already mounted
	if err := setupFlyVolMount(); err != nil {
		return fmt.Errorf("failed to setup /dev/fly_vol mount: %w", err)
	}

	// Boot the system
	if err := app.system.Boot(app.ctx); err != nil {
		return fmt.Errorf("failed to boot system: %w", err)
	}

	// Start resource monitor
	if app.resourceMonitor != nil {
		app.resourceMonitor.Start(app.ctx)
	}

	// Set up signal handling
	signalCh := make(chan os.Signal, 1)
	signal.Notify(signalCh, syscall.SIGTERM, syscall.SIGINT, syscall.SIGHUP)

	// Set up process monitoring
	processDoneCh := make(chan error, 1)
	go func() {
		err := app.system.Wait()
		processDoneCh <- err
	}()

	// Wait for shutdown trigger
	for {
		select {
		case <-app.ctx.Done():
			// Context cancelled, shutdown
			app.logger.Debug("Context cancelled, shutting down")
			return app.shutdown(1)

		case err := <-processDoneCh:
			// Process exited
			exitCode := 0
			if err != nil {
				app.logger.Error("Process exited with error", "error", err)
				// Extract exit code from error if available
				if exitErr, ok := err.(*exec.ExitError); ok {
					if status, ok := exitErr.Sys().(syscall.WaitStatus); ok {
						exitCode = status.ExitStatus()
						app.logger.Info("Process exit code", "exitCode", exitCode)
					}
				}
			} else {
				app.logger.Info("Process exited normally")
			}

			// Decide what to do based on keepAliveOnError setting
			if !app.system.IsRestoring() {
				if app.keepAliveOnError {
					app.logger.Info("Process exited, but keeping server alive (SPRITE_KEEP_ALIVE_ON_ERROR=true)")
					app.logger.Info("Server is still running and accepting API requests")
					// Only restart monitoring if a process is actually running
					if app.system.IsProcessRunning() {
						go func() {
							err := app.system.Wait()
							processDoneCh <- err
						}()
					}
				} else {
					app.logger.Info("Process exited, stopping application...", "exitCode", exitCode)
					return app.shutdown(exitCode)
				}
			} else {
				// If restoring, only restart monitoring if a process is running
				if app.system.IsProcessRunning() {
					go func() {
						err := app.system.Wait()
						processDoneCh <- err
					}()
				}
			}

		case sig := <-signalCh:
			switch sig {
			case syscall.SIGTERM, syscall.SIGINT:
				app.logger.Info("Received shutdown signal", "signal", sig)
				exitCode := 0
				if sig == syscall.SIGTERM {
					exitCode = 143 // 128 + 15
				} else if sig == syscall.SIGINT {
					exitCode = 130 // 128 + 2
				}
				return app.shutdown(exitCode)

			default:
				// Forward other signals to system
				if err := app.system.ForwardSignal(sig); err != nil {
					app.logger.Warn("Failed to forward signal", "signal", sig, "error", err)
				}
			}
		}
	}
}

// shutdown performs graceful shutdown
func (app *Application) shutdown(exitCode int) error {
	app.logger.Info("Shutting down application")

	if err := syscall.Sync(); err != nil {
		app.logger.Error("Failed to sync filesystem", "error", err)
	}

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

	// Stop socket server
	if app.sockServer != nil {
		if err := app.sockServer.Stop(); err != nil {
			app.logger.Error("Failed to stop socket server", "error", err)
		}
	}

	// Close services manager
	if app.servicesManager != nil {
		if err := app.servicesManager.Close(); err != nil {
			app.logger.Error("Failed to close services manager", "error", err)
		}
	}

	// Stop admin channel
	if app.adminChannel != nil {
		if err := app.adminChannel.Stop(); err != nil {
			app.logger.Error("Failed to stop admin channel", "error", err)
		}
	}

	// Shutdown system (stops process and JuiceFS)
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	if err := app.system.Shutdown(ctx); err != nil {
		app.logger.Error("Failed to shutdown system", "error", err)
	}
	cancel()

	// Stop zombie reaper
	if err := app.reaper.Stop(1 * time.Second); err != nil {
		app.logger.Warn("Failed to stop reaper", "error", err)
	}

	app.logger.Info("Application stopped", "exitCode", exitCode)
	os.Exit(exitCode)
	return nil
}

// Command-line parsing and main

func parseCommandLine() (Config, error) {
	config := Config{}

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

		// Debug: Show what's in the config file
		// Note: Using default logger since tap logger isn't initialized yet
		slog.Debug("Loading config from file", "file", configFile)
		slog.Debug("Config file contents", "contents", string(data))

		var fileConfig struct {
			LogLevel           string   `json:"log_level"`
			LogJSON            bool     `json:"log_json"`
			APIListen          string   `json:"api_listen_addr"`
			ProcessCmd         []string `json:"process_command"`
			ProcessDir         string   `json:"process_working_dir"`
			ProcessEnv         []string `json:"process_environment"`
			ExecWrapperCommand []string `json:"exec_wrapper_command"`

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
			OverlayEnabled       bool     `json:"overlay_enabled"`
			OverlayImageSize     string   `json:"overlay_image_size"`
			OverlayLowerPath     string   `json:"overlay_lower_path"`
			OverlayLowerPaths    []string `json:"overlay_lower_paths"`
			OverlayTargetPath    string   `json:"overlay_target_path"`
			OverlaySkipOverlayFS bool     `json:"overlay_skip_overlayfs"`

			// Proxy configuration
			ProxyLocalhostIPv4 string `json:"proxy_localhost_ipv4"`
			ProxyLocalhostIPv6 string `json:"proxy_localhost_ipv6"`
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

		config.JuiceFSBaseDir = fileConfig.JuiceFSBaseDir
		config.JuiceFSLocalMode = fileConfig.JuiceFSLocalMode
		config.S3AccessKey = fileConfig.S3AccessKey
		config.S3SecretAccessKey = fileConfig.S3SecretAccessKey
		config.S3EndpointURL = fileConfig.S3EndpointURL
		config.S3Bucket = fileConfig.S3Bucket
		config.OverlayEnabled = fileConfig.OverlayEnabled
		config.OverlayImageSize = fileConfig.OverlayImageSize
		config.OverlayLowerPath = fileConfig.OverlayLowerPath
		config.OverlayLowerPaths = fileConfig.OverlayLowerPaths
		config.OverlayTargetPath = fileConfig.OverlayTargetPath
		config.OverlaySkipOverlayFS = fileConfig.OverlaySkipOverlayFS

		config.ProxyLocalhostIPv4 = fileConfig.ProxyLocalhostIPv4
		config.ProxyLocalhostIPv6 = fileConfig.ProxyLocalhostIPv6
	}

	// Apply LOG_LEVEL environment variable if set
	if logLevel := os.Getenv("LOG_LEVEL"); logLevel != "" {
		switch strings.ToLower(logLevel) {
		case "debug":
			config.LogLevel = slog.LevelDebug
		case "info":
			config.LogLevel = slog.LevelInfo
		case "warn", "warning":
			config.LogLevel = slog.LevelWarn
		case "error":
			config.LogLevel = slog.LevelError
		default:
			// Invalid log level - ignore and use default
			fmt.Fprintf(os.Stderr, "Warning: Invalid LOG_LEVEL '%s', using default\n", logLevel)
		}
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
	config.AdminToken = os.Getenv("SPRITE_HTTP_ADMIN_TOKEN")

	// JuiceFS configuration - environment overrides file config
	juicefsBaseDir := os.Getenv("SPRITE_WRITE_DIR")
	if juicefsBaseDir != "" {
		config.JuiceFSBaseDir = filepath.Join(juicefsBaseDir, "juicefs")
	}
	if juicefsDirFlag != "" {
		config.JuiceFSBaseDir = juicefsDirFlag
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
	// New environment variable for multiple lower paths (colon-separated)
	if overlayLowerPaths := os.Getenv("SPRITE_OVERLAY_LOWER_PATHS"); overlayLowerPaths != "" {
		config.OverlayLowerPaths = strings.Split(overlayLowerPaths, ":")
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

// fileExists checks if a file exists
func fileExists(path string) bool {
	_, err := os.Stat(path)
	return err == nil
}

// setupFlyVolMount sets up the /dev/fly_vol bind mount if not already mounted
func setupFlyVolMount() error {
	flyVolPath := "/dev/fly_vol"
	upperLayerPath := "/.fly-upper-layer/fly_vol"
	logger := slog.Default()

	logger.Debug("Checking if /dev/fly_vol is already mounted", "path", flyVolPath)
	// Check if /dev/fly_vol is already a mount point
	cmd := exec.Command("mountpoint", "-q", flyVolPath)
	if err := cmd.Run(); err == nil {
		// Already mounted
		logger.Debug("/dev/fly_vol is already mounted, skipping setup")
		return nil
	}
	logger.Debug("/dev/fly_vol is not mounted, proceeding with setup")

	// Create the upper layer directory
	logger.Debug("Creating upper layer directory", "path", upperLayerPath)
	if err := os.MkdirAll(upperLayerPath, 0755); err != nil {
		logger.Error("Failed to create upper layer directory", "path", upperLayerPath, "error", err)
		return fmt.Errorf("failed to create upper layer directory: %w", err)
	}

	// Check if upper layer exists and get info
	if info, err := os.Stat(upperLayerPath); err == nil {
		logger.Debug("Upper layer directory created/exists", "path", upperLayerPath, "mode", info.Mode())
	}

	// Create /dev/fly_vol directory
	logger.Debug("Creating /dev/fly_vol directory", "path", flyVolPath)
	if err := os.MkdirAll(flyVolPath, 0755); err != nil {
		logger.Error("Failed to create /dev/fly_vol directory", "path", flyVolPath, "error", err)
		return fmt.Errorf("failed to create /dev/fly_vol directory: %w", err)
	}

	// Bind mount /.fly-upper-layer/fly_vol to /dev/fly_vol
	logger.Info("Performing bind mount", "source", upperLayerPath, "target", flyVolPath)
	cmd = exec.Command("mount", "--bind", upperLayerPath, flyVolPath)
	if output, err := cmd.CombinedOutput(); err != nil {
		logger.Error("Failed to bind mount /dev/fly_vol",
			"source", upperLayerPath,
			"target", flyVolPath,
			"error", err,
			"output", string(output))
		return fmt.Errorf("failed to bind mount /dev/fly_vol: %w", err)
	}

	logger.Info("/dev/fly_vol bind mount completed successfully", "source", upperLayerPath, "target", flyVolPath)
	return nil
}

func main() {
	// Create crash log file for debugging
	crashLogFile, err := os.OpenFile("/tmp/sprite-env-crash.log", os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0644)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Warning: Could not create crash log file: %v\n", err)
	} else {
		defer crashLogFile.Close()
	}

	// We'll set up enhanced panic recovery after the app is created
	var app *Application

	// Set up panic recovery
	defer func() {
		if r := recover(); r != nil {
			crashMsg := fmt.Sprintf("PANIC at %s: %v\n", time.Now().Format(time.RFC3339), r)
			fmt.Fprintf(os.Stderr, "%s", crashMsg)

			stackTrace := debug.Stack()
			if crashLogFile != nil {
				crashLogFile.WriteString(crashMsg)
				crashLogFile.WriteString(fmt.Sprintf("Stack trace:\n%s\n", stackTrace))
				crashLogFile.Sync()
			}

			// Try to report crash if app and crash reporter are available
			if app != nil && app.system != nil {
				// Create crash report
				report := &tap.CrashReport{
					ExitCode:   1,
					Error:      fmt.Sprintf("panic: %v", r),
					StackTrace: string(stackTrace),
				}

				if crashReporter := app.system.GetCrashReporter(); crashReporter != nil {
					ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
					defer cancel()

					if err := crashReporter.ReportGoPanic(ctx, report); err != nil {
						fmt.Fprintf(os.Stderr, "Failed to report panic: %v\n", err)
					}
				}

				// Send notification to admin channel
				if app.adminChannel != nil {
					app.adminChannel.SendActivityEvent("go_runtime_panic", report.ToMap())
				}
			}

			os.Exit(1)
		}
	}()

	// Log startup
	startupMsg := fmt.Sprintf("Starting sprite-env at %s\n", time.Now().Format(time.RFC3339))
	fmt.Printf("%s", startupMsg)
	if crashLogFile != nil {
		crashLogFile.WriteString(startupMsg)
		crashLogFile.Sync()
	}

	config, err := parseCommandLine()
	if err != nil {
		errMsg := fmt.Sprintf("Error parsing command line: %v\n", err)
		fmt.Fprintf(os.Stderr, "%s", errMsg)
		if crashLogFile != nil {
			crashLogFile.WriteString(errMsg)
			crashLogFile.Sync()
		}
		flag.Usage()
		os.Exit(1)
	}

	if crashLogFile != nil {
		crashLogFile.WriteString(fmt.Sprintf("Config parsed successfully at %s\n", time.Now().Format(time.RFC3339)))
		crashLogFile.Sync()
	}

	app, err = NewApplication(config)
	if err != nil {
		errMsg := fmt.Sprintf("Failed to create application: %v\n", err)
		fmt.Fprintf(os.Stderr, "%s", errMsg)
		if crashLogFile != nil {
			crashLogFile.WriteString(errMsg)
			crashLogFile.Sync()
		}
		os.Exit(1)
	}

	if crashLogFile != nil {
		crashLogFile.WriteString(fmt.Sprintf("Application created successfully at %s\n", time.Now().Format(time.RFC3339)))
		crashLogFile.Sync()
	}

	// Run the application
	if err := app.Run(); err != nil {
		errMsg := fmt.Sprintf("Application run failed: %v\n", err)
		fmt.Fprintf(os.Stderr, "%s", errMsg)
		if crashLogFile != nil {
			crashLogFile.WriteString(errMsg)
			crashLogFile.Sync()
		}
		// Error already logged, just exit
		os.Exit(1)
	}

	if crashLogFile != nil {
		crashLogFile.WriteString(fmt.Sprintf("Application completed normally at %s\n", time.Now().Format(time.RFC3339)))
		crashLogFile.Sync()
	}
}
