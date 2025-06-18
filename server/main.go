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
	"syscall"
	"time"

	"sprite-env/lib"
	"sprite-env/lib/adapters"
	"sprite-env/lib/api"
	"sprite-env/lib/managers"
)

// version is set at build time via ldflags
var version = "dev"

// outputTrace outputs a single trace event
func outputTrace(transition lib.StateTransition) {
	// Create a simple flat trace with just the transition info
	trace := map[string]interface{}{
		"source":  transition.Name,
		"from":    transition.From,
		"to":      transition.To,
		"trigger": transition.Trigger,
	}

	now := time.Now()
	fmt.Fprintf(os.Stdout, "TLA+ trace: %v %s\n", trace, now.Format("2006-01-02 15:04:05.000000000 MST"))
	// Output JSON to stderr
	if jsonBytes, err := json.Marshal(trace); err == nil {
		fmt.Fprintf(os.Stderr, "%s\n", jsonBytes)
	}
}

// Application holds the main application state
type Application struct {
	systemState *managers.SystemState
	apiServer   *api.Server
	logger      *slog.Logger
	ctx         context.Context
	cancel      context.CancelFunc
	config      lib.ApplicationConfig
	monitor     lib.StateMonitor // State monitor for TLA tracing
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

	// Create TLA monitor if tracing is enabled
	var monitor lib.StateMonitor
	if config.TLATrace {
		logger.Info("TLA+ trace logging enabled")
		monitor = lib.NewStateMonitor(outputTrace)
	}

	if config.Debug {
		logger.Info("Debug logging enabled")
	}

	// Create components dynamically from configuration
	components := make([]managers.ManagedComponent, 0, len(config.Components))

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
		// Cast adapters.Component to managers.ManagedComponent (interfaces are compatible)
		components = append(components, component)

		if config.Debug {
			logger.Info("Created component", "component", componentName)
		}
	}

	// Create process state manager for the supervised process
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

	// Create process state manager with monitor
	var processMonitors []lib.StateMonitor
	if monitor != nil {
		processMonitors = []lib.StateMonitor{monitor}
	}
	processStateMachine := managers.NewProcessState(managers.ProcessStateConfig{
		Process: process,
	}, processMonitors)

	// Create system state manager with monitor
	systemConfig := managers.SystemConfig{
		ProcessState: processStateMachine,
		Components:   components,
	}
	var systemMonitors []lib.StateMonitor
	if monitor != nil {
		systemMonitors = append(systemMonitors, monitor)
	}

	systemState := managers.NewSystemState(systemConfig, systemMonitors)

	// Create API server if listen address is specified
	var apiServer *api.Server
	if config.APIListenAddr != "" {
		apiServer = api.NewServer(config.APIListenAddr, systemState, logger, &config)
	}

	app := &Application{
		systemState: systemState,
		apiServer:   apiServer,
		logger:      logger,
		ctx:         ctx,
		cancel:      cancel,
		config:      config,
		monitor:     monitor,
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

	// Trigger the initial system startup sequence
	app.logger.Info("Starting system state machine...")
	app.systemState.Fire("SystemStarting")

	app.logger.Info("System state machine started, awaiting component readiness...")
	app.logger.Info("Application started successfully")
	return nil
}

// Stop stops the application gracefully
func (app *Application) Stop(ctx context.Context) error {
	app.logger.Info("Stopping sprite-env application")

	// Request system shutdown using the trigger-based API
	app.systemState.Fire("ShutdownRequested")

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
	var tlaTrace bool
	var logJSON bool
	var gracefulShutdownTimeout time.Duration
	var listenAddr string
	var configFile string
	var showVersion bool

	flag.StringVar(&configFile, "config", "", "JSON configuration file path")
	flag.StringVar(&componentsDir, "components-dir", "", "Directory containing component subdirectories with management scripts")
	flag.StringVar(&testDir, "test-dir", "", "Test directory containing component subdirectories (alias for -components-dir)")
	flag.BoolVar(&debug, "debug", false, "Enable debug logging")
	flag.BoolVar(&tlaTrace, "tla-trace", false, "Enable TLA+ state change tracing")
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
	if tlaTrace {
		config.TLATrace = true
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

	// Wait for either signal or system to reach terminal state
	exitCode := 0

	// Create a channel to receive exit codes from the system state machine
	systemExitChan := make(chan int, 1)

	// Set up the system state machine to send exit codes to our channel
	app.systemState.SetExitChannel(systemExitChan)

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
		if sig == syscall.SIGTERM {
			exitCode = 143 // 128 + 15
		} else if sig == syscall.SIGINT {
			exitCode = 130 // 128 + 2
		}

	case <-ctx.Done():
		app.logger.Info("Context cancelled, shutting down")

	case exitCode = <-systemExitChan:
		app.logger.Info("System reached terminal state", "exitCode", exitCode)
		cancel()

		// Perform cleanup when system reaches terminal state
		shutdownCtx, shutdownCancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer shutdownCancel()

		if err := app.Stop(shutdownCtx); err != nil {
			app.logger.Error("Error during cleanup", "error", err)
		}
	}

	app.logger.Info("Application exited", "exitCode", exitCode)
	os.Exit(exitCode)
}
