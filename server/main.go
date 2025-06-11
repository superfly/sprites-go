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

	"github.com/qmuntal/stateless"
)

// TLAState holds the complete system state for tracing
type TLAState struct {
	SystemState       string            `json:"systemState"`
	ComponentSetState string            `json:"componentSetState"`
	ProcessState      string            `json:"processState"`
	ComponentStates   map[string]string `json:"-"` // Individual component states (flattened into stateMap)
}

// Application holds the main application state
type Application struct {
	systemStateMachine       *lib.SystemState
	componentSetStateMachine *lib.ComponentSetState
	processStateMachine      *lib.ProcessState
	httpServer               *lib.HTTPServer
	logger                   *slog.Logger
	ctx                      context.Context
	cancel                   context.CancelFunc
	config                   ApplicationConfig
	tlaState                 *TLAState // Current state for tracing
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
	ProcessCommand           []string
	ProcessWorkingDir        string
	ProcessEnvironment       []string
	ProcessRestartMaxRetries int
	ProcessRestartBackoffMax time.Duration
}

// TLATrace represents a single state transition trace
type TLATrace struct {
	Source      string                 `json:"source"`      // Which state machine caused this trace
	Transition  TransitionInfo         `json:"transition"`  // What transition occurred
	SystemState map[string]interface{} `json:"systemState"` // Current state snapshot
}

// TransitionInfo captures the transition details
type TransitionInfo struct {
	From    string `json:"from"`    // Previous state
	To      string `json:"to"`      // New state
	Trigger string `json:"trigger"` // What triggered the transition
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

	// TODO: Handle TLA-trace and debug output configuration
	if config.TLATrace {
		logger.Info("TLA+ trace logging enabled - TODO: implement TLA trace output")
	}
	if config.Debug {
		logger.Info("Debug logging enabled")
	}

	// Create component state machines dynamically from configuration
	components := make(map[string]*lib.ComponentState)

	for componentName, componentScripts := range config.Components {
		componentConfig := lib.ComponentConfig{
			StartCommand:      componentScripts.StartCommand,
			ReadyCommand:      componentScripts.ReadyCommand,
			CheckpointCommand: componentScripts.CheckpointCommand,
			RestoreCommand:    componentScripts.RestoreCommand,
		}
		componentStateMachine := lib.NewComponentState(componentConfig)
		components[componentName] = componentStateMachine

		if config.Debug {
			logger.Info("Created component state machine", "component", componentName)
		}
	}
	componentSetStateMachine := lib.NewComponentSetState(components)

	// Create process state machine for the supervised process
	processConfig := lib.ProcessConfig{
		Command:                 config.ProcessCommand,
		MaxRetries:              config.ProcessRestartMaxRetries,
		RestartDelay:            time.Second, // Start with 1 second delay
		GracefulShutdownTimeout: 30 * time.Second,
	}
	// TODO: Handle ProcessWorkingDir and ProcessEnvironment - not currently supported in ProcessConfig
	if config.ProcessWorkingDir != "" {
		logger.Info("Process working directory configuration not yet supported", "workingDir", config.ProcessWorkingDir)
	}
	if len(config.ProcessEnvironment) > 0 {
		logger.Info("Process environment configuration not yet supported", "env", config.ProcessEnvironment)
	}

	processStateMachine := lib.NewProcessState(processConfig)

	// Create system state machine
	systemStateMachine := lib.NewSystemState(componentSetStateMachine, processStateMachine)

	// Create HTTP server for monitoring
	httpServer := lib.NewHTTPServer(":8080", systemStateMachine, logger)

	app := &Application{
		systemStateMachine:       systemStateMachine,
		componentSetStateMachine: componentSetStateMachine,
		processStateMachine:      processStateMachine,
		httpServer:               httpServer,
		logger:                   logger,
		ctx:                      ctx,
		cancel:                   cancel,
		config:                   config,
		tlaState: &TLAState{
			ComponentStates: make(map[string]string),
		},
	}

	// Set up TLA tracing if enabled
	app.setupTLATracing()

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

	// System state machine automatically starts and coordinates to Running state
	// when components are ready - no manual intervention needed
	app.logger.Info("System state machine started, awaiting component readiness...")

	app.logger.Info("Application started successfully")
	return nil
}

// Stop stops the application gracefully
func (app *Application) Stop(ctx context.Context) error {
	app.logger.Info("Stopping sprite-env application")

	// Request system shutdown using the trigger-based API
	if err := app.systemStateMachine.Fire(lib.SystemTriggerShutdownRequested); err != nil {
		app.logger.Error("Failed to request system shutdown", "error", err)
		// Continue with other cleanup
	}

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

	flag.StringVar(&componentsDir, "components-dir", "", "Directory containing component subdirectories with management scripts")
	flag.StringVar(&testDir, "test-dir", "", "Test directory containing component subdirectories (alias for -components-dir)")
	flag.BoolVar(&debug, "debug", false, "Enable debug logging")
	flag.BoolVar(&tlaTrace, "tla-trace", false, "Enable TLA+ state change tracing")
	flag.BoolVar(&logJSON, "log-json", false, "Output logs in JSON format")
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
		ProcessCommand:           args,
		ProcessWorkingDir:        "",
		ProcessEnvironment:       []string{},
		ProcessRestartMaxRetries: 3,
		ProcessRestartBackoffMax: 60 * time.Second,
	}

	return config, nil
}

// setupTLATracing sets up TLA+ trace output when enabled
func (app *Application) setupTLATracing() {
	if !app.config.TLATrace {
		return
	}

	// Initialize the state once
	app.updateTLAState()

	// Set up callbacks with transition information
	// System state machine changes
	app.systemStateMachine.AddStateChangeCallback(func(transition stateless.Transition) {
		app.outputTLATrace("SystemStateMachine", transition)
	})

	// Component set state machine changes
	app.componentSetStateMachine.AddStateChangeCallback(func(transition stateless.Transition) {
		app.outputTLATrace("ComponentSetStateMachine", transition)
	})

	// Process state machine changes
	app.processStateMachine.AddStateChangeCallback(func(transition stateless.Transition) {
		app.outputTLATrace("ProcessStateMachine", transition)
	})

	// Individual component state machine changes
	app.componentSetStateMachine.AddComponentTransitionCallback(func(componentName string, transition stateless.Transition) {
		app.outputTLATrace(componentName, transition)
	})
}

// updateTLAState updates the cached TLA state from all state machines
func (app *Application) updateTLAState() {
	// Update system-level states
	app.tlaState.SystemState = string(app.systemStateMachine.GetState())
	app.tlaState.ComponentSetState = string(app.systemStateMachine.GetComponentSetState())
	app.tlaState.ProcessState = string(app.systemStateMachine.GetProcessState())

	// Update component states
	componentStates := app.componentSetStateMachine.GetComponentStates()
	for componentName, state := range componentStates {
		app.tlaState.ComponentStates[componentName] = string(state)
	}
}

// mapHierarchicalState converts hierarchical SystemStateMachine states to simple superstates for tracing
func mapHierarchicalState(state string) string {
	switch {
	case state == "Initializing.ComponentsStarting":
		return "Initializing"
	case state == "Initializing.ComponentsReady":
		return "Initializing" // Still in Initializing superstate
	case state == "Ready.ProcessStarting":
		return "Ready"
	case state == "Running.Both":
		return "Running"
	case state == "ShuttingDown.ComponentsStopping":
		return "ShuttingDown"
	case state == "ShuttingDown.ProcessStopping":
		return "ShuttingDown"
	default:
		// For simple states (like Error, Shutdown) return as-is
		return state
	}
}

// outputTLATrace outputs a state transition trace as a flat map
func (app *Application) outputTLATrace(source string, transition stateless.Transition) {
	fromState := fmt.Sprintf("%v", transition.Source)
	toState := fmt.Sprintf("%v", transition.Destination)

	// For SystemStateMachine, convert hierarchical states to simple superstates
	if source == "SystemStateMachine" {
		fromState = mapHierarchicalState(fromState)
		toState = mapHierarchicalState(toState)
	}

	// Create a simple flat trace with just the transition info
	trace := map[string]interface{}{
		"source":  source,
		"from":    fromState,
		"to":      toState,
		"trigger": fmt.Sprintf("%v", transition.Trigger),
	}

	// Output JSON to stderr
	if jsonBytes, err := json.Marshal(trace); err == nil {
		fmt.Fprintf(os.Stderr, "%s\n", jsonBytes)
	}
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

	// Wait for signal or context cancellation
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
			os.Exit(143) // 128 + 15
		} else if sig == syscall.SIGINT {
			os.Exit(130) // 128 + 2
		}

	case <-ctx.Done():
		app.logger.Info("Context cancelled, shutting down")
	}

	app.logger.Info("Application exited cleanly")
}
