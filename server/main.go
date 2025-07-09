package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"log/slog"
	"os"
	"os/signal"
	"path/filepath"
	"runtime/debug"
	"strings"
	"syscall"
	"time"

	serverapi "github.com/sprite-env/server/api"
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

	// Container configuration
	ContainerEnabled    bool
	ContainerSocketDir  string
	ContainerTTYTimeout time.Duration

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

	// Dynamic configuration
	DynamicConfigPath string // Path to persist dynamic configuration

	// Transcript configuration
	TranscriptDBPath string // Path to SQLite database file
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
	return []string{"/mnt/app-image"}
}

// Application represents the main application
type Application struct {
	config    Config
	logger    *slog.Logger
	system    *System
	reaper    *Reaper
	apiServer *serverapi.Server
	ctx       context.Context
	cancel    context.CancelFunc

	// State
	keepAliveOnError bool
	dynamicConfig    bool // Whether we're in dynamic config mode
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
		config:           config,
		logger:           logger,
		ctx:              ctx,
		cancel:           cancel,
		keepAliveOnError: config.KeepAliveOnError,
		dynamicConfig:    config.DynamicConfigPath != "",
	}

	// Create Reaper instance
	app.reaper = NewReaper(logger)

	// Create System instance with minimal config if in dynamic mode
	var systemConfig SystemConfig
	if config.DynamicConfigPath == "" {
		// Normal mode - populate config from parsed values
		systemConfig = SystemConfig{
			ProcessCommand:                 config.ProcessCommand,
			ProcessWorkingDir:              config.ProcessWorkingDir,
			ProcessEnvironment:             config.ProcessEnvironment,
			ProcessGracefulShutdownTimeout: config.ProcessGracefulShutdownTimeout,
			ContainerEnabled:               config.ContainerEnabled,
			ContainerSocketDir:             config.ContainerSocketDir,
			ContainerTTYTimeout:            config.ContainerTTYTimeout,
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
	}
	// In dynamic mode with existing config file, systemConfig will be populated from the file

	system, err := NewSystemWithDynamicConfig(systemConfig, config.DynamicConfigPath, logger, app.reaper)
	if err != nil {
		return nil, fmt.Errorf("failed to create system: %w", err)
	}

	// Set transcript DB path
	system.SetTranscriptDBPath(config.TranscriptDBPath)

	app.system = system

	// Set up API server if configured
	if config.APIListenAddr != "" {
		apiConfig := serverapi.Config{
			ListenAddr:         config.APIListenAddr,
			APIToken:           config.APIToken,
			AdminToken:         config.AdminToken,
			MaxWaitTime:        30 * time.Second,
			ExecWrapperCommand: config.ExecWrapperCommand,
		}

		apiServer, err := serverapi.NewServer(apiConfig, app.system, logger)
		if err != nil {
			return nil, fmt.Errorf("failed to create API server: %w", err)
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

	// Handle dynamic configuration mode
	if app.dynamicConfig && !fileExists(app.config.DynamicConfigPath) {
		app.logger.Info("Dynamic configuration mode enabled, waiting for configuration",
			"config_path", app.config.DynamicConfigPath)

		// In dynamic config mode without existing config, only start the API server
		// The /configure endpoint will handle booting the system
		if app.apiServer != nil {
			go func() {
				if err := app.apiServer.Start(); err != nil {
					app.logger.Error("API server error", "error", err)
					// Trigger shutdown if API server fails
					app.cancel()
				}
			}()
		} else {
			return fmt.Errorf("API server must be configured when using dynamic configuration mode")
		}
	} else {
		// Normal boot sequence
		if err := app.system.Boot(app.ctx); err != nil {
			return fmt.Errorf("failed to boot system: %w", err)
		}

		// Start API server if configured
		if app.apiServer != nil {
			go func() {
				if err := app.apiServer.Start(); err != nil {
					app.logger.Error("API server error", "error", err)
					// Trigger shutdown if API server fails
					app.cancel()
				}
			}()
		}
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
			if err != nil {
				app.logger.Error("Process exited with error", "error", err)
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
					app.logger.Info("Process exited, stopping application...")
					return app.shutdown(0)
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
		dynamicConfigPath       string
	)

	flag.StringVar(&configFile, "config", "", "JSON configuration file")
	flag.BoolVar(&debug, "debug", false, "Enable debug logging")
	flag.BoolVar(&logJSON, "log-json", false, "Output logs in JSON format")
	flag.StringVar(&listenAddr, "listen", "", "API server listen address")
	flag.DurationVar(&gracefulShutdownTimeout, "graceful-shutdown-timeout", 30*time.Second, "Process graceful shutdown timeout")
	flag.StringVar(&juicefsDirFlag, "juicefs-dir", "", "JuiceFS base directory")
	flag.BoolVar(&showVersion, "version", false, "Show version and exit")
	flag.StringVar(&dynamicConfigPath, "dynamic-config", "", "Path to persist dynamic configuration (enables dynamic config mode)")
	flag.Parse()

	if showVersion {
		fmt.Printf("sprite-env version %s\n", version)
		os.Exit(0)
	}

	// Set dynamic config path
	config.DynamicConfigPath = dynamicConfigPath

	// If dynamic config mode is enabled and config file exists, load it
	if dynamicConfigPath != "" && fileExists(dynamicConfigPath) {
		configFile = dynamicConfigPath
	}

	// Load from config file if specified
	if configFile != "" {
		data, err := os.ReadFile(configFile)
		if err != nil {
			return config, fmt.Errorf("failed to read config file: %w", err)
		}

		// Debug: Show what's in the config file
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

			// Container configuration
			ContainerEnabled    bool   `json:"container_enabled"`
			ContainerSocketDir  string `json:"container_socket_dir"`
			ContainerTTYTimeout string `json:"container_tty_timeout"`

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

			// Transcript configuration
			TranscriptDBPath string `json:"transcript_db_path"`
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

		// Container configuration
		config.ContainerEnabled = fileConfig.ContainerEnabled
		config.ContainerSocketDir = fileConfig.ContainerSocketDir
		if fileConfig.ContainerTTYTimeout != "" {
			if timeout, err := time.ParseDuration(fileConfig.ContainerTTYTimeout); err == nil {
				config.ContainerTTYTimeout = timeout
			}
		}

		// Debug: Log container config values parsed from file
		slog.Debug("Container config from file",
			"enabled", config.ContainerEnabled,
			"socket_dir", config.ContainerSocketDir,
			"tty_timeout", config.ContainerTTYTimeout)

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
		config.TranscriptDBPath = fileConfig.TranscriptDBPath
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

	// Transcript configuration - environment overrides file config
	if transcriptDBPath := os.Getenv("SPRITE_TRANSCRIPT_DB_PATH"); transcriptDBPath != "" {
		config.TranscriptDBPath = transcriptDBPath
	}

	// Debug configuration
	if os.Getenv("SPRITE_KEEP_ALIVE_ON_ERROR") == "true" {
		config.KeepAliveOnError = true
	}

	// Validate - now API token is required if API server is configured
	if config.APIListenAddr != "" && config.APIToken == "" {
		return config, fmt.Errorf("API token must be set when API server is enabled")
	}

	if config.TranscriptDBPath == "" {
		config.TranscriptDBPath = "/var/log/transcripts.db"
	}

	return config, nil
}

// fileExists checks if a file exists
func fileExists(path string) bool {
	_, err := os.Stat(path)
	return err == nil
}

func main() {
	// Create crash log file for debugging
	crashLogFile, err := os.OpenFile("/tmp/sprite-env-crash.log", os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0644)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Warning: Could not create crash log file: %v\n", err)
	} else {
		defer crashLogFile.Close()
	}

	// Set up panic recovery
	defer func() {
		if r := recover(); r != nil {
			crashMsg := fmt.Sprintf("PANIC at %s: %v\n", time.Now().Format(time.RFC3339), r)
			fmt.Fprintf(os.Stderr, "%s", crashMsg)
			if crashLogFile != nil {
				crashLogFile.WriteString(crashMsg)
				crashLogFile.WriteString(fmt.Sprintf("Stack trace:\n%s\n", debug.Stack()))
				crashLogFile.Sync()
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

	app, err := NewApplication(config)
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
