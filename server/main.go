package main

import (
	"context"
	"flag"
	"fmt"
	"log/slog"
	"os"
	"os/signal"
	"path/filepath"
	"syscall"
	"time"

	"sprite-env/lib"
	"sprite-env/lib/adapters"
	"sprite-env/lib/api"
	"sprite-env/lib/managers"
)

// version is set at build time via ldflags
var version = "dev"

// Application holds the main application state
type Application struct {
	processState    *managers.ProcessState
	componentState  *managers.ComponentState
	apiServer       *api.Server
	logger          *slog.Logger
	ctx             context.Context
	cancel          context.CancelFunc
	config          lib.ApplicationConfig
}

// NewApplication creates a new application instance
func NewApplication(config lib.ApplicationConfig) *Application {
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

	// Create context for the application
	ctx, cancel := context.WithCancel(context.Background())

	if config.Debug {
		logger.Info("Debug logging enabled")
	}

	// Create exactly one component (if configured)
	var componentState *managers.ComponentState
	if len(config.Components) > 0 {
		// For simplicity, we'll use the first component configured
		// In a real scenario, you might want to handle multiple components differently
		for componentName, componentScripts := range config.Components {
			// Create concrete CmdComponent with configuration
			componentConfig := adapters.CmdComponentConfig{
				Name:              componentName,
				StartCommand:      componentScripts.StartCommand,
				ReadyCommand:      componentScripts.ReadyCommand,
				CheckpointCommand: componentScripts.CheckpointCommand,
				RestoreCommand:    componentScripts.RestoreCommand,
			}
			component := adapters.NewCmdComponent(componentConfig)
			
			// Create component state manager
			componentState = managers.NewComponentState(componentName+"Component", component)
			
			if config.Debug {
				logger.Info("Created component", "component", componentName)
			}
			
			// Only handle the first component for now
			break
		}
	}

	// Create process state manager for the supervised process
	var processState *managers.ProcessState
	if len(config.ProcessCommand) > 0 {
		processConfig := adapters.ProcessConfig{
			Command:                 config.ProcessCommand,
			MaxRetries:              config.ProcessRestartMaxRetries,
			RestartDelay:            time.Second, // Start with 1 second delay
			GracefulShutdownTimeout: config.ProcessGracefulShutdownTimeout,
		}
		// TODO: Handle ProcessWorkingDir and ProcessEnvironment - not currently supported in ProcessConfig
		if config.ProcessWorkingDir != "" {
			logger.Info("Process working directory configuration not yet supported", "workingDir", config.ProcessWorkingDir)
		}
		if len(config.ProcessEnvironment) > 0 {
			logger.Info("Process environment configuration not yet supported", "env", config.ProcessEnvironment)
		}

		process := adapters.NewProcess(processConfig)
		processState = managers.NewProcessState(managers.ProcessStateConfig{
			Process: process,
		})
	}

	// Create API server with the process state
	var apiServer *api.Server
	if config.APIListenAddr != "" {
		apiServer = api.NewServer(config.APIListenAddr, processState, componentState, logger, &config)
	}

	app := &Application{
		processState:   processState,
		componentState: componentState,
		apiServer:      apiServer,
		logger:         logger,
		ctx:            ctx,
		cancel:         cancel,
		config:         config,
	}

	return app
}

// Start starts the application
func (app *Application) Start(ctx context.Context) error {
	app.logger.Info("Starting sprite-env application", "version", version)

	// Start API server if configured
	if app.apiServer != nil {
		if err := app.apiServer.Start(); err != nil {
			app.logger.Error("Failed to start API server", "error", err)
			return err
		}
	}

	// Start component state manager first (if configured)
	if app.componentState != nil {
		app.logger.Info("Starting component state machine...")
		if err := app.componentState.Fire("Starting"); err != nil {
			app.logger.Error("Failed to start component", "error", err)
			return err
		}
		
		// Wait for component to be running
		// In a real implementation, you might want to poll or use events
		// For now, we'll check the state after a brief delay
		time.Sleep(2 * time.Second)
		
		currentState := app.componentState.MustState().(string)
		if currentState == "Running" {
			app.logger.Info("Component is running, starting process...")
			
			// After component is running, start the process
			if app.processState != nil {
				if err := app.processState.Fire("Starting"); err != nil {
					app.logger.Error("Failed to start process", "error", err)
					return err
				}
			}
		} else {
			app.logger.Error("Component failed to reach running state", "state", currentState)
			return fmt.Errorf("component failed to start, current state: %s", currentState)
		}
	} else if app.processState != nil {
		// No component configured, just start the process
		app.logger.Info("Starting process state machine...")
		if err := app.processState.Fire("Starting"); err != nil {
			app.logger.Error("Failed to start process", "error", err)
			return err
		}
	}

	app.logger.Info("Application started successfully")
	return nil
}

// Stop stops the application gracefully
func (app *Application) Stop(ctx context.Context) error {
	app.logger.Info("Stopping sprite-env application")

	// Stop process first
	if app.processState != nil {
		if err := app.processState.Fire("Stopping"); err != nil {
			app.logger.Error("Failed to stop process", "error", err)
		}
	}

	// Then stop component
	if app.componentState != nil {
		if err := app.componentState.Fire("Stopping"); err != nil {
			app.logger.Error("Failed to stop component", "error", err)
		}
	}

	// Stop API server if running
	if app.apiServer != nil {
		if err := app.apiServer.Stop(ctx); err != nil {
			app.logger.Error("Failed to shutdown API server", "error", err)
		}
	}

	// Cancel application context
	app.cancel()

	app.logger.Info("Application stopped")
	return nil
}

// parseCommandLineArgs parses command line arguments and returns configuration
func parseCommandLineArgs() (lib.ApplicationConfig, error) {
	var componentsDir string
	var testDir string
	var debug bool
	var logJSON bool
	var gracefulShutdownTimeout time.Duration
	var listenAddr string
	var configFile string
	var showVersion bool

	flag.StringVar(&configFile, "config", "", "JSON configuration file path")
	flag.StringVar(&componentsDir, "components-dir", "", "Directory containing component subdirectories with management scripts")
	flag.StringVar(&testDir, "test-dir", "", "Test directory containing component subdirectories (alias for -components-dir)")
	flag.BoolVar(&debug, "debug", false, "Enable debug logging")
	flag.BoolVar(&logJSON, "log-json", false, "Output logs in JSON format")
	flag.DurationVar(&gracefulShutdownTimeout, "graceful-shutdown-timeout", 30*time.Second, "Timeout for graceful process shutdown before SIGKILL")
	flag.StringVar(&listenAddr, "listen", "", "HTTP API server listen address (e.g., 0.0.0.0:8090)")
	flag.BoolVar(&showVersion, "version", false, "Display version and exit")
	flag.Parse()

	// Handle version flag
	if showVersion {
		fmt.Printf("sprite-env version %s\n", version)
		os.Exit(0)
	}

	var config lib.ApplicationConfig

	// If config file is specified, load from it first
	if configFile != "" {
		loader := lib.NewConfigLoader()
		loadedConfig, err := loader.LoadFromFile(configFile)
		if err != nil {
			return lib.ApplicationConfig{}, fmt.Errorf("failed to load config file: %w", err)
		}
		config = *loadedConfig
	} else {
		// Initialize with defaults if no config file
		config = lib.ApplicationConfig{
			LogLevel:                       slog.LevelInfo,
			ProcessRestartMaxRetries:       3,
			ProcessRestartBackoffMax:       60 * time.Second,
			ProcessGracefulShutdownTimeout: 30 * time.Second,
			Components:                     make(map[string]lib.ComponentScripts),
		}
	}

	// Apply command line overrides (these always take precedence)
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
	if gracefulShutdownTimeout != 30*time.Second {
		config.ProcessGracefulShutdownTimeout = gracefulShutdownTimeout
	}

	// Handle process command from remaining arguments
	args := flag.Args()
	if len(args) > 0 {
		config.ProcessCommand = args
	}

	// Handle components directory if specified
	// This allows mixing config file with component discovery
	if componentsDir != "" || testDir != "" {
		// Use testDir if specified, otherwise use componentsDir
		if testDir != "" {
			componentsDir = testDir
		}

		// Helper function to check and resolve script paths
		checkScript := func(componentName, scriptType, componentDir string) []string {
			// Try script without extension first
			scriptPathNoExt := filepath.Join(componentDir, scriptType)
			if absPath, err := filepath.Abs(scriptPathNoExt); err == nil {
				if _, err := os.Stat(absPath); err == nil {
					if config.Debug {
						fmt.Printf("Found %s %s script: %s\n", componentName, scriptType, absPath)
					}
					return []string{absPath}
				} else if config.Debug {
					fmt.Printf("%s %s script not found: %s\n", componentName, scriptType, absPath)
				}
			}

			// Try script with .sh extension as fallback
			scriptPathWithSh := filepath.Join(componentDir, scriptType+".sh")
			if absPath, err := filepath.Abs(scriptPathWithSh); err == nil {
				if _, err := os.Stat(absPath); err == nil {
					if config.Debug {
						fmt.Printf("Found %s %s script: %s\n", componentName, scriptType, absPath)
					}
					return []string{absPath}
				} else if config.Debug {
					fmt.Printf("%s %s script not found: %s\n", componentName, scriptType, absPath)
				}
			}

			return nil
		}

		// Discover component directories
		entries, err := os.ReadDir(componentsDir)
		if err != nil {
			return lib.ApplicationConfig{}, fmt.Errorf("failed to read components directory %s: %w", componentsDir, err)
		}

		// Initialize components map if nil
		if config.Components == nil {
			config.Components = make(map[string]lib.ComponentScripts)
		}

		for _, entry := range entries {
			if !entry.IsDir() {
				continue // Skip non-directories
			}

			componentName := entry.Name()
			componentDir := filepath.Join(componentsDir, componentName)

			// Discover scripts for this component
			startCommand := checkScript(componentName, "start", componentDir)
			readyCommand := checkScript(componentName, "ready", componentDir)
			checkpointCommand := checkScript(componentName, "checkpoint", componentDir)
			restoreCommand := checkScript(componentName, "restore", componentDir)

			// Validate that required start command exists
			if len(startCommand) == 0 {
				return lib.ApplicationConfig{}, fmt.Errorf("%s start script is required but not found at: %s or %s", componentName, filepath.Join(componentDir, "start"), filepath.Join(componentDir, "start.sh"))
			}

			// Add or override component (CLI discovered components take precedence)
			config.Components[componentName] = lib.ComponentScripts{
				StartCommand:      startCommand,
				ReadyCommand:      readyCommand,
				CheckpointCommand: checkpointCommand,
				RestoreCommand:    restoreCommand,
			}

			if config.Debug {
				fmt.Printf("Configured component: %s\n", componentName)
			}
		}
	}

	// Validate final configuration
	if len(config.Components) == 0 && len(config.ProcessCommand) == 0 {
		return lib.ApplicationConfig{}, fmt.Errorf("either components or supervised process command must be specified")
	}

	return config, nil
}

func main() {
	// Parse command line arguments
	config, err := parseCommandLineArgs()
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		fmt.Fprintf(os.Stderr, "\nUsage:\n")
		fmt.Fprintf(os.Stderr, "  %s -components-dir <dir> [options] -- <supervised-process-command>\n", os.Args[0])
		fmt.Fprintf(os.Stderr, "  %s -config <file.json> [options] [-- <supervised-process-command>]\n", os.Args[0])
		fmt.Fprintf(os.Stderr, "  %s -config <file.json> -components-dir <dir> [options] [-- <supervised-process-command>]\n", os.Args[0])
		fmt.Fprintf(os.Stderr, "\nOptions can be mixed: use -config for base settings and override with CLI flags.\n")
		os.Exit(1)
	}

	// Create application
	app := NewApplication(config)

	// Set up signal handling
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	sigChan := make(chan os.Signal, 1)
	signal.Notify(sigChan, syscall.SIGTERM, syscall.SIGINT)

	// Start application
	if err := app.Start(ctx); err != nil {
		app.logger.Error("Failed to start application", "error", err)
		os.Exit(1)
	}

	// Wait for signal
	select {
	case sig := <-sigChan:
		app.logger.Info("Received signal, shutting down", "signal", sig)
		cancel()

		// Graceful shutdown with timeout
		shutdownCtx, shutdownCancel := context.WithTimeout(context.Background(), 30*time.Second)
		defer shutdownCancel()

		if err := app.Stop(shutdownCtx); err != nil {
			app.logger.Error("Error during shutdown", "error", err)
			os.Exit(1)
		}

		// Set exit code based on signal
		exitCode := 0
		if sig == syscall.SIGTERM {
			exitCode = 143 // 128 + 15
		} else if sig == syscall.SIGINT {
			exitCode = 130 // 128 + 2
		}
		app.logger.Info("Application exited", "exitCode", exitCode)
		os.Exit(exitCode)

	case <-ctx.Done():
		app.logger.Info("Context cancelled, shutting down")
		shutdownCtx, shutdownCancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer shutdownCancel()

		if err := app.Stop(shutdownCtx); err != nil {
			app.logger.Error("Error during cleanup", "error", err)
		}
	}
}
