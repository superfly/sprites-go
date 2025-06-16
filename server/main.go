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

	"sprite-env/lib/adapters"
	"sprite-env/lib/managers"
)

// outputTrace outputs a single trace event
func outputTrace(transition managers.StateTransition) {
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

// SystemStateAdapter adapts managers.SystemStateManager to match adapters.SystemStateMachine interface
type SystemStateAdapter struct {
	*managers.SystemState
}

// Fire adapts the stateless.Fire method to match the expected interface
func (adapter *SystemStateAdapter) Fire(trigger interface{}) error {
	// Convert interface{} trigger to string for the SystemStateManager
	return adapter.SystemState.Fire(fmt.Sprintf("%v", trigger))
}

// GetState adapts the GetState method to return interface{}
func (adapter *SystemStateAdapter) GetState() interface{} {
	return adapter.SystemState.MustState()
}

// GetErrorType adapts the GetErrorType method to return interface{}
func (adapter *SystemStateAdapter) GetErrorType() interface{} {
	// SystemStateManager doesn't have an error type, return current state
	return adapter.SystemState.MustState()
}

// Application holds the main application state
type Application struct {
	systemStateMachine *managers.SystemState
	httpServer         *adapters.HTTPServer
	logger             *slog.Logger
	ctx                context.Context
	cancel             context.CancelFunc
	config             ApplicationConfig
	monitor            managers.StateMonitor // State monitor for TLA tracing
}

// ComponentScripts holds the script commands for a component
type ComponentScripts struct {
	StartCommand      []string
	ReadyCommand      []string
	CheckpointCommand []string
	RestoreCommand    []string
}

// ApplicationConfig holds configuration for the application
type ApplicationConfig struct {
	// Logging configuration
	LogLevel slog.Level
	LogJSON  bool
	TLATrace bool
	Debug    bool

	// Dynamic component configurations (keyed by component name)
	Components map[string]ComponentScripts

	// Process configuration
	ProcessCommand                 []string
	ProcessWorkingDir              string
	ProcessEnvironment             []string
	ProcessRestartMaxRetries       int
	ProcessRestartBackoffMax       time.Duration
	ProcessGracefulShutdownTimeout time.Duration
}

// NewApplication creates a new application instance
func NewApplication(config ApplicationConfig) *Application {
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
	var monitor managers.StateMonitor
	if config.TLATrace {
		logger.Info("TLA+ trace logging enabled")
		monitor = managers.NewStateMonitor(outputTrace)
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
	var processMonitors []managers.StateMonitor
	if monitor != nil {
		processMonitors = []managers.StateMonitor{monitor}
	}
	processStateMachine := managers.NewProcessState(managers.ProcessStateConfig{
		Process: process,
	}, processMonitors)

	// Create system state manager with monitor
	systemConfig := managers.SystemConfig{
		ProcessState: processStateMachine,
		Components:   components,
	}
	var systemMonitors []managers.StateMonitor
	if monitor != nil {
		systemMonitors = append(systemMonitors, monitor)
	}

	systemStateMachine := managers.NewSystemState(systemConfig, systemMonitors)

	// Create adapter for HTTP server interface compatibility
	systemStateAdapter := &SystemStateAdapter{SystemState: systemStateMachine}

	// Create HTTP server for monitoring
	httpServer := adapters.NewHTTPServer(":8080", systemStateAdapter, logger)

	app := &Application{
		systemStateMachine: systemStateMachine,
		httpServer:         httpServer,
		logger:             logger,
		ctx:                ctx,
		cancel:             cancel,
		config:             config,
		monitor:            monitor,
	}

	return app
}

// Start starts the application
func (app *Application) Start(ctx context.Context) error {
	app.logger.Info("Starting sprite-env application")

	// Start HTTP server
	if err := app.httpServer.Start(); err != nil {
		app.logger.Error("Failed to start HTTP server", "error", err)
		return err
	}

	// Trigger the initial system startup sequence
	app.logger.Info("Starting system state machine...")
	app.systemStateMachine.Fire("SystemStarting")

	app.logger.Info("System state machine started, awaiting component readiness...")
	app.logger.Info("Application started successfully")
	return nil
}

// Stop stops the application gracefully
func (app *Application) Stop(ctx context.Context) error {
	app.logger.Info("Stopping sprite-env application")

	// Request system shutdown using the trigger-based API
	app.systemStateMachine.Fire("ShutdownRequested")

	// Stop HTTP server
	if err := app.httpServer.Stop(ctx); err != nil {
		app.logger.Error("Failed to shutdown HTTP server", "error", err)
	}

	// Cancel application context
	app.cancel()

	app.logger.Info("Application stopped")
	return nil
}

// parseCommandLineArgs parses command line arguments and returns configuration
func parseCommandLineArgs() (ApplicationConfig, error) {
	var componentsDir string
	var testDir string
	var debug bool
	var tlaTrace bool
	var logJSON bool
	var gracefulShutdownTimeout time.Duration

	flag.StringVar(&componentsDir, "components-dir", "", "Directory containing component subdirectories with management scripts")
	flag.StringVar(&testDir, "test-dir", "", "Test directory containing component subdirectories (alias for -components-dir)")
	flag.BoolVar(&debug, "debug", false, "Enable debug logging")
	flag.BoolVar(&tlaTrace, "tla-trace", false, "Enable TLA+ state change tracing")
	flag.BoolVar(&logJSON, "log-json", false, "Output logs in JSON format")
	flag.DurationVar(&gracefulShutdownTimeout, "graceful-shutdown-timeout", 30*time.Second, "Timeout for graceful process shutdown before SIGKILL")
	flag.Parse()

	// Get supervised process path from remaining arguments
	args := flag.Args()
	if len(args) == 0 {
		return ApplicationConfig{}, fmt.Errorf("supervised process command is required")
	}

	// Handle both -components-dir and -test-dir flags
	if componentsDir == "" && testDir == "" {
		return ApplicationConfig{}, fmt.Errorf("either -components-dir or -test-dir is required")
	}

	// Use testDir if specified, otherwise use componentsDir
	if testDir != "" {
		componentsDir = testDir
	}

	// Determine log level
	logLevel := slog.LevelInfo
	if debug {
		logLevel = slog.LevelDebug
	}

	// Helper function to check and resolve script paths (tries both with and without .sh extension)
	checkScript := func(componentName, scriptType, componentDir string) []string {
		// Try script without extension first
		scriptPathNoExt := filepath.Join(componentDir, scriptType)
		if absPath, err := filepath.Abs(scriptPathNoExt); err == nil {
			if _, err := os.Stat(absPath); err == nil {
				if debug {
					fmt.Printf("Found %s %s script: %s\n", componentName, scriptType, absPath)
				}
				return []string{absPath}
			} else if debug {
				fmt.Printf("%s %s script not found: %s\n", componentName, scriptType, absPath)
			}
		}

		// Try script with .sh extension as fallback
		scriptPathWithSh := filepath.Join(componentDir, scriptType+".sh")
		if absPath, err := filepath.Abs(scriptPathWithSh); err == nil {
			if _, err := os.Stat(absPath); err == nil {
				if debug {
					fmt.Printf("Found %s %s script: %s\n", componentName, scriptType, absPath)
				}
				return []string{absPath}
			} else if debug {
				fmt.Printf("%s %s script not found: %s\n", componentName, scriptType, absPath)
			}
		}

		return nil
	}

	// Discover component directories
	entries, err := os.ReadDir(componentsDir)
	if err != nil {
		return ApplicationConfig{}, fmt.Errorf("failed to read components directory %s: %w", componentsDir, err)
	}

	components := make(map[string]ComponentScripts)

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
			return ApplicationConfig{}, fmt.Errorf("%s start script is required but not found at: %s or %s", componentName, filepath.Join(componentDir, "start"), filepath.Join(componentDir, "start.sh"))
		}

		components[componentName] = ComponentScripts{
			StartCommand:      startCommand,
			ReadyCommand:      readyCommand,
			CheckpointCommand: checkpointCommand,
			RestoreCommand:    restoreCommand,
		}

		if debug {
			fmt.Printf("Configured component: %s\n", componentName)
		}
	}

	if len(components) == 0 {
		return ApplicationConfig{}, fmt.Errorf("no component directories found in %s", componentsDir)
	}

	// Build configuration
	config := ApplicationConfig{
		LogLevel: logLevel,
		LogJSON:  logJSON,
		TLATrace: tlaTrace,
		Debug:    debug,

		// Dynamic component configurations
		Components: components,

		// Process configuration
		ProcessCommand:                 args,
		ProcessWorkingDir:              "",
		ProcessEnvironment:             []string{},
		ProcessRestartMaxRetries:       3,
		ProcessRestartBackoffMax:       60 * time.Second,
		ProcessGracefulShutdownTimeout: gracefulShutdownTimeout,
	}

	return config, nil
}

func main() {
	// Parse command line arguments
	config, err := parseCommandLineArgs()
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		fmt.Fprintf(os.Stderr, "Usage: %s -components-dir <dir> [options] -- <supervised-process-command>\n", os.Args[0])
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
	app.systemStateMachine.SetExitChannel(systemExitChan)

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
