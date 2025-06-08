package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"log"
	"net/http"
	"os"
	"os/signal"
	"path/filepath"
	"syscall"
	"time"

	"sprite-env/lib"
	"sprite-env/lib/states"
)

// Signal types as defined in the TLA+ spec
const (
	SignalNone     = "None"
	SignalGraceful = "SIGTERM"
	SignalForce    = "SIGKILL"
)

// States as defined in the TLA+ spec
const (
	StateInitializing  = "Initializing"
	StateRunning       = "Running"
	StateCheckpointing = "Checkpointing"
	StateRestoring     = "Restoring"
	StateError         = "Error"
	StateShutdown      = "Shutdown"
)

// ProcessStates as defined in the TLA+ spec
const (
	ProcessStopped   = "Stopped"
	ProcessStarting  = "Starting"
	ProcessRunning   = "Running"
	ProcessStopping  = "Stopping"
	ProcessSignaling = "Signaling"
	ProcessCrashed   = "Crashed"
	ProcessExited    = "Exited"
	ProcessKilled    = "Killed"
	ProcessError     = "Error"
)

// ErrorTypes as defined in the TLA+ spec
const (
	ErrorNone            = "None"
	ErrorDBError         = "DBError"
	ErrorFSError         = "FSError"
	ErrorProcessError    = "ProcessError"
	ErrorProcessCrash    = "ProcessCrash"
	ErrorProcessKilled   = "ProcessKilled"
	ErrorCheckpointError = "CheckpointError"
	ErrorRestoreError    = "RestoreError"
	ErrorStartupError    = "StartupError"
)

// SpriteEnv represents the main application environment
type SpriteEnv struct {
	globalStateManager     *states.GlobalStateManager
	componentSetManager    *states.ComponentSetStateManager
	overallStateManager    *lib.StateManager // New: manages overall state via aggregation
	processStateManager    *lib.StateManager // New: tracks process state
	checkpointStateManager *lib.StateManager // New: tracks checkpoint flag
	restoreStateManager    *lib.StateManager // New: tracks restore flag
	shutdownStateManager   *lib.StateManager // New: tracks shutdown flag
	errorTypeManager       *lib.StateManager // New: tracks error type
	componentSet           *lib.ComponentSet
	supervisedProcess      *lib.ProcessManager
	ctx                    context.Context
	cancel                 context.CancelFunc
	debug                  bool
	tlaTrace               bool
	server                 *http.Server
}

// NewSpriteEnv creates a new SpriteEnv instance
func NewSpriteEnv() *SpriteEnv {
	ctx, cancel := context.WithCancel(context.Background())

	// Create state managers (keeping existing ones for compatibility)
	globalStateManager := states.NewGlobalStateManager(false)
	componentSetManager := states.NewComponentSetStateManager(false)

	// Set up cross-references for centralized tracing
	globalStateManager.SetComponentSetManager(componentSetManager)
	componentSetManager.SetGlobalStateManager(globalStateManager)

	// Initialize all component states with default "Initializing" state
	dbComponent := states.NewComponentState(states.StateInitializing)
	fsComponent := states.NewComponentState(states.StateInitializing)
	componentSetManager.AddComponent("DB", dbComponent)
	componentSetManager.AddComponent("FS", fsComponent)

	// Create new StateManagers for overall state management
	debug := false // Will be set later
	processStateManager := lib.NewStateManager(lib.SMProcessStopped, debug)
	checkpointStateManager := lib.NewStateManager(lib.BooleanFalse, debug)
	restoreStateManager := lib.NewStateManager(lib.BooleanFalse, debug)
	shutdownStateManager := lib.NewStateManager(lib.BooleanFalse, debug)
	errorTypeManager := lib.NewStateManager(lib.ErrorTypeNone, debug)

	// Create overall state manager with aggregation
	overallStateManager := lib.NewStateManager(lib.GlobalInitializing, debug)

	// Start all StateManagers
	processStateManager.Start()
	checkpointStateManager.Start()
	restoreStateManager.Start()
	shutdownStateManager.Start()
	errorTypeManager.Start()
	overallStateManager.Start()

	env := &SpriteEnv{
		globalStateManager:     globalStateManager,
		componentSetManager:    componentSetManager,
		overallStateManager:    overallStateManager,
		processStateManager:    processStateManager,
		checkpointStateManager: checkpointStateManager,
		restoreStateManager:    restoreStateManager,
		shutdownStateManager:   shutdownStateManager,
		errorTypeManager:       errorTypeManager,
		ctx:                    ctx,
		cancel:                 cancel,
		server:                 &http.Server{Addr: ":8080"},
	}

	// Set up state transitions after env is created
	env.setupOverallStateTransitions()

	return env
}

// setupOverallStateTransitions sets up explicit state transitions for overall state
func (s *SpriteEnv) setupOverallStateTransitions() {
	// Set up trace emission callback
	s.overallStateManager.OnTransition(func(oldState, newState lib.State) {
		if s.tlaTrace {
			s.emitTLATrace(newState.String())
		}
	})

	// Start with Initializing state
	s.overallStateManager.SetState(lib.GlobalInitializing)
}

// emitTLATrace emits TLA+ traces with current state
func (s *SpriteEnv) emitTLATrace(overallState string) {
	// Get current states from all sources
	var componentSetState, dbState, fsState, processState string
	var processExitCode int
	var checkpointInProgress, restoreInProgress, shutdownInProgress, exitRequested bool
	var signalReceived string
	var dbShutdownTimeout, fsShutdownTimeout int
	var dbForceKilled, fsForceKilled bool
	var restartAttempt, restartDelay int
	var errorType string

	// Get component states
	if s.componentSet != nil {
		componentStates := s.componentSet.GetState()
		componentSetState = s.componentSet.GetOverallState()
		if dbStateVal, exists := componentStates["DB"]; exists {
			dbState = dbStateVal
		}
		if fsStateVal, exists := componentStates["FS"]; exists {
			fsState = fsStateVal
		}
	}

	// Get process state
	if s.supervisedProcess != nil {
		processState = s.supervisedProcess.GetState().String()
		processExitCode = s.supervisedProcess.GetExitCode()
	}

	// Get flag states
	checkpointInProgress = s.checkpointStateManager.GetState().String() == "true"
	restoreInProgress = s.restoreStateManager.GetState().String() == "true"
	shutdownInProgress = s.shutdownStateManager.GetState().String() == "true"
	errorType = s.errorTypeManager.GetState().String()

	// Get additional state from global state manager (for compatibility)
	if s.globalStateManager != nil && s.globalStateManager.State != nil {
		exitRequested = s.globalStateManager.State.ExitRequested
		signalReceived = s.globalStateManager.State.SignalReceived
		dbShutdownTimeout = s.globalStateManager.State.DBShutdownTimeout
		fsShutdownTimeout = s.globalStateManager.State.FSShutdownTimeout
		dbForceKilled = s.globalStateManager.State.DBForceKilled
		fsForceKilled = s.globalStateManager.State.FSForceKilled
		restartAttempt = s.globalStateManager.State.RestartAttempt
		restartDelay = s.globalStateManager.State.RestartDelay
	}

	// Create TLA+ trace in JSON format
	trace := map[string]interface{}{
		"overallState":         overallState,
		"componentSetState":    componentSetState,
		"dbState":              dbState,
		"fsState":              fsState,
		"processState":         processState,
		"processExitCode":      processExitCode,
		"checkpointInProgress": checkpointInProgress,
		"restoreInProgress":    restoreInProgress,
		"errorType":            errorType,
		"restartAttempt":       restartAttempt,
		"restartDelay":         restartDelay,
		"shutdownInProgress":   shutdownInProgress,
		"exitRequested":        exitRequested,
		"signalReceived":       signalReceived,
		"dbShutdownTimeout":    dbShutdownTimeout,
		"fsShutdownTimeout":    fsShutdownTimeout,
		"dbForceKilled":        dbForceKilled,
		"fsForceKilled":        fsForceKilled,
	}

	// Output to stderr in JSON format (atomic write)
	jsonBytes, err := json.Marshal(trace)
	if err == nil {
		os.Stderr.Write(jsonBytes)
		os.Stderr.Write([]byte("\n"))
	}
}

// SetComponentSet sets the component set to be managed
func (s *SpriteEnv) SetComponentSet(cs *lib.ComponentSet) {
	s.componentSet = cs

	// Listen for component set state changes to trigger explicit state transitions
	go func() {
		for state := range cs.StateChanged() {
			if s.debug {
				fmt.Printf("DEBUG: ComponentSet state changed to: %s\n", state.String())
			}
			s.handleComponentSetStateChange(state.String())
		}
	}()
}

// triggerOverallStateUpdate triggers a recalculation of overall state
func (s *SpriteEnv) triggerOverallStateUpdate() {
	// Update error type based on current states
	errorType := s.determineErrorType()

	// Convert to ErrorTypeState
	var errorTypeState lib.ErrorTypeState
	switch errorType {
	case ErrorNone:
		errorTypeState = lib.ErrorTypeNone
	case ErrorDBError:
		errorTypeState = lib.ErrorTypeDBError
	case ErrorFSError:
		errorTypeState = lib.ErrorTypeFSError
	case ErrorProcessError:
		errorTypeState = lib.ErrorTypeProcessError
	case ErrorProcessCrash:
		errorTypeState = lib.ErrorTypeProcessCrash
	case ErrorProcessKilled:
		errorTypeState = lib.ErrorTypeProcessKilled
	case ErrorCheckpointError:
		errorTypeState = lib.ErrorTypeCheckpointError
	case ErrorRestoreError:
		errorTypeState = lib.ErrorTypeRestoreError
	case ErrorStartupError:
		errorTypeState = lib.ErrorTypeStartupError
	default:
		errorTypeState = lib.ErrorTypeNone
	}

	// Update error type manager (this will trigger overall state aggregation)
	// This is the key - any child state change triggers the aggregation function
	s.errorTypeManager.SetState(errorTypeState)
}

// handleComponentSetStateChange handles explicit state transitions based on component set changes
func (s *SpriteEnv) handleComponentSetStateChange(componentSetState string) {
	currentOverallState := s.overallStateManager.GetState().String()

	if s.debug {
		fmt.Printf("DEBUG: Handling component set state change: %s (current overall: %s)\n", componentSetState, currentOverallState)
	}

	// Only transition to Running if we're currently Initializing and all components are ready
	if currentOverallState == "Initializing" && componentSetState == "Running" {
		// Check if supervised process is also ready to start
		if s.supervisedProcess != nil {
			processState := s.supervisedProcess.GetState().String()
			if processState == "Initializing" {
				// Start the supervised process
				if s.debug {
					fmt.Printf("DEBUG: Components ready, starting supervised process\n")
				}
				if err := s.supervisedProcess.Start(); err != nil {
					if s.debug {
						fmt.Printf("DEBUG: Error starting supervised process: %v\n", err)
					}
					return
				}
			}
		}
	}
}

// SetSupervisedProcess sets the supervised process to be managed
func (s *SpriteEnv) SetSupervisedProcess(proc *lib.ProcessManager) {
	s.supervisedProcess = proc
}

// updateState is no longer needed - state management is handled by the aggregation system

// determineErrorType implements the DetermineErrorType logic from the TLA+ spec
func (s *SpriteEnv) determineErrorType() string {
	state := s.globalStateManager.State

	if s.componentSet != nil {
		componentStates := s.componentSet.GetState()
		if dbState, exists := componentStates["DB"]; exists && dbState == StateError {
			return ErrorDBError
		}
		if fsState, exists := componentStates["FS"]; exists && fsState == StateError {
			return ErrorFSError
		}
	}

	if s.supervisedProcess != nil {
		processState := s.supervisedProcess.GetState().String()
		if processState == ProcessError {
			return ErrorProcessError
		}
		if processState == ProcessCrashed {
			return ErrorProcessCrash
		}
		if processState == ProcessKilled {
			return ErrorProcessKilled
		}
	}

	if state.CheckpointInProgress && s.componentSet != nil {
		componentStates := s.componentSet.GetState()
		if dbState, exists := componentStates["DB"]; exists && dbState == StateError {
			return ErrorCheckpointError
		}
		if fsState, exists := componentStates["FS"]; exists && fsState == StateError {
			return ErrorCheckpointError
		}
	}

	if state.RestoreInProgress && s.componentSet != nil {
		componentStates := s.componentSet.GetState()
		if dbState, exists := componentStates["DB"]; exists && dbState == StateError {
			return ErrorRestoreError
		}
		if fsState, exists := componentStates["FS"]; exists && fsState == StateError {
			return ErrorRestoreError
		}
	}

	return ErrorNone
}

// handleSignal handles system signals according to the TLA+ spec
func (s *SpriteEnv) handleSignal(sig os.Signal) {
	if s.debug {
		fmt.Printf("DEBUG: Signal handler received: %v\n", sig)
	}

	// Handle graceful shutdown signals
	if sig == syscall.SIGTERM || sig == syscall.SIGINT {
		// Start shutdown sequence
		s.startShutdownSequence()
	}
}

// startShutdownSequence starts the explicit shutdown sequence
func (s *SpriteEnv) startShutdownSequence() {
	if s.debug {
		fmt.Printf("DEBUG: Starting shutdown sequence\n")
	}

	// First stop the supervised process
	if s.supervisedProcess != nil {
		if s.debug {
			fmt.Printf("DEBUG: Stopping supervised process\n")
		}
		if err := s.supervisedProcess.Stop(); err != nil {
			if s.debug {
				fmt.Printf("DEBUG: Error stopping supervised process: %v\n", err)
			}
		}
	}

	// Start a goroutine to handle the rest of shutdown after process stops
	go func() {
		// Wait a bit for process to finish stopping
		time.Sleep(500 * time.Millisecond)

		// Now stop components
		if s.componentSet != nil {
			if s.debug {
				fmt.Printf("DEBUG: Stopping components\n")
			}
			if err := s.componentSet.Stop(); err != nil {
				if s.debug {
					fmt.Printf("DEBUG: Error stopping components: %v\n", err)
				}
			}
		}

		// Final transition to Shutdown state
		s.overallStateManager.SetState(lib.GlobalShutdown)

		// Shutdown HTTP server
		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		defer cancel()
		if err := s.server.Shutdown(ctx); err != nil {
			if s.debug {
				fmt.Printf("DEBUG: Error shutting down HTTP server: %v\n", err)
			}
		}

		// Cancel context to stop all goroutines
		s.cancel()

		// Exit cleanly
		os.Exit(0)
	}()
}

// StartCheckpoint implements checkpoint operation according to TLA+ spec
func (s *SpriteEnv) StartCheckpoint() error {
	// Check if operations are already in progress
	checkpointInProgress := s.checkpointStateManager.GetState().String() == "true"
	restoreInProgress := s.restoreStateManager.GetState().String() == "true"

	if checkpointInProgress || restoreInProgress {
		return fmt.Errorf("operation already in progress")
	}

	// Update both legacy and new state managers
	s.globalStateManager.State.CheckpointInProgress = true
	s.checkpointStateManager.SetState(lib.BooleanTrue)

	return nil
}

// StartRestore implements restore operation according to TLA+ spec
func (s *SpriteEnv) StartRestore() error {
	// Check if operations are already in progress
	checkpointInProgress := s.checkpointStateManager.GetState().String() == "true"
	restoreInProgress := s.restoreStateManager.GetState().String() == "true"

	if checkpointInProgress || restoreInProgress {
		return fmt.Errorf("operation already in progress")
	}

	// Update both legacy and new state managers
	s.globalStateManager.State.RestoreInProgress = true
	s.restoreStateManager.SetState(lib.BooleanTrue)

	return nil
}

// UpdateComponentState updates a single component's state and records the change
func (s *SpriteEnv) UpdateComponentState(component string, newState string, oldState string) {
	if s.debug {
		fmt.Printf("DEBUG: %s state changed from %s to %s\n", component, oldState, newState)
	}
	// Just trigger overall state recalculation - let aggregation handle the rest
	s.triggerOverallStateUpdate()
}

// UpdateProcessState updates the process state and handles explicit overall state transitions
func (s *SpriteEnv) UpdateProcessState(newState string, oldState string) {
	if s.debug {
		fmt.Printf("DEBUG: Process state changed from %s to %s\n", oldState, newState)
	}

	s.handleProcessStateChange(oldState, newState)
}

// handleProcessStateChange handles explicit overall state transitions based on process state changes
func (s *SpriteEnv) handleProcessStateChange(oldState, newState string) {
	currentOverallState := s.overallStateManager.GetState().String()

	if s.debug {
		fmt.Printf("DEBUG: Handling process state change: %s -> %s (current overall: %s)\n", oldState, newState, currentOverallState)
	}

	// Handle specific state transitions
	switch newState {
	case "Running":
		// If process becomes running and we have components running, transition to overall Running
		if currentOverallState == "Initializing" && s.componentSet != nil {
			componentSetState := s.componentSet.GetOverallState()
			if componentSetState == "Running" {
				s.overallStateManager.SetState(lib.GlobalRunning)
			}
		}
	case "Stopping":
		// When process starts stopping, transition to ShuttingDown
		if currentOverallState == "Running" {
			s.overallStateManager.SetState(lib.GlobalShuttingDown)
		}
	case "Stopped":
		// When process is stopped, continue shutdown sequence
		if currentOverallState == "ShuttingDown" {
			// Process is stopped, but we stay in ShuttingDown until components are stopped too
			if s.debug {
				fmt.Printf("DEBUG: Process stopped, continuing shutdown of components\n")
			}
		}
	}
}

// Start starts all components and the supervised process
func (s *SpriteEnv) Start() error {
	if s.debug {
		fmt.Printf("DEBUG: Starting all components\n")
	}

	// Start components
	if s.componentSet != nil {
		if err := s.componentSet.Start(); err != nil {
			if s.debug {
				fmt.Printf("DEBUG: Error starting components: %v\n", err)
			}
			return err
		}
	}

	return nil
}

func main() {
	var exitCode int // Track exit code for graceful return
	defer func() {
		if exitCode != 0 {
			os.Exit(exitCode)
		}
	}()

	// Parse command line arguments
	var testDir string
	var debug bool
	var tlaTrace bool
	flag.StringVar(&testDir, "test-dir", "", "Directory containing test scripts")
	flag.BoolVar(&debug, "debug", false, "Enable debug logging")
	flag.BoolVar(&tlaTrace, "tla-trace", false, "Enable TLA+ state change tracing")
	flag.Parse()

	// Set up logging
	if debug {
		log.SetOutput(os.Stdout)
	}

	// Get supervised process path from remaining arguments after --
	var supervisedProcessPath string
	args := flag.Args()
	if len(args) > 0 {
		supervisedProcessPath = args[0]
	}

	if testDir != "" && supervisedProcessPath == "" {
		log.Printf("ERROR: When using -test-dir, supervised process path must be provided after --")
		log.Printf("Usage: %s -test-dir <dir> -debug -- <supervised-process-path>", os.Args[0])
		exitCode = 1
		return
	}

	env := NewSpriteEnv()
	env.debug = debug
	env.tlaTrace = tlaTrace
	env.globalStateManager.TLATrace = tlaTrace
	env.componentSetManager.TLATrace = tlaTrace

	// Note: StateManager debug flag is set during creation via NewStateManager

	// Set up signal handling
	sigChan := make(chan os.Signal, 1)
	signal.Notify(sigChan, syscall.SIGTERM, syscall.SIGINT)

	// Start HTTP server for state inspection
	http.HandleFunc("/state", func(w http.ResponseWriter, r *http.Request) {
		json.NewEncoder(w).Encode(env.globalStateManager.State)
	})

	http.HandleFunc("/trace", func(w http.ResponseWriter, r *http.Request) {
		json.NewEncoder(w).Encode(env.globalStateManager.Changes)
	})

	go func() {
		if err := env.server.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			log.Printf("HTTP server error: %v", err)
		}
	}()

	// Initialize components if test directory is provided
	if testDir != "" {
		if debug {
			fmt.Printf("DEBUG: Using test scripts from %s\n", testDir)
			fmt.Printf("DEBUG: Using supervised process: %s\n", supervisedProcessPath)
		}

		// PHASE 1: Initialize everything
		if debug {
			fmt.Printf("DEBUG: Initializing components and process\n")
		}

		// Create ComponentSet for storage components
		componentSet := lib.NewComponentSet(debug)

		// Create individual components
		dbManager := lib.NewComponentManager(env, debug, "DB", filepath.Join(testDir, "db", "start.sh"), filepath.Join(testDir, "db", "ready.sh"))
		fsManager := lib.NewComponentManager(env, debug, "FS", filepath.Join(testDir, "fs", "start.sh"), filepath.Join(testDir, "fs", "ready.sh"))

		// Add components to the set
		componentSet.AddComponent("DB", dbManager)
		componentSet.AddComponent("FS", fsManager)

		// Create supervised process
		supervisedProcess := lib.NewProcessManager(env, debug, supervisedProcessPath, "")

		// Set up environment
		env.SetComponentSet(componentSet)
		env.SetSupervisedProcess(supervisedProcess)

		// PHASE 2: Start everything
		if debug {
			fmt.Printf("DEBUG: Starting components and process\n")
		}

		// Start components
		if err := componentSet.Start(); err != nil {
			log.Printf("Failed to start components: %v", err)
			exitCode = 1
			return
		}
	}

	// State management is now handled by explicit state transitions

	// Wait for all components to be ready
	if env.componentSet != nil {
		// Wait for all components to be ready
		for _, component := range env.componentSet.GetComponents() {
			<-component.GetReadyChan()
		}
		// Now transition to Running
		env.componentSet.TransitionToRunning()
	}

	// Main event loop
	for {
		select {
		case sig := <-sigChan:
			if debug {
				fmt.Printf("DEBUG: Received signal: %v\n", sig)
			}

			// Set exit code based on signal (Unix convention: 128 + signal number)
			if sig == syscall.SIGTERM {
				exitCode = 128 + 15 // 143
			} else if sig == syscall.SIGINT {
				exitCode = 128 + 2 // 130
			}

			// Handle signals according to spec
			env.handleSignal(sig)

		case <-env.ctx.Done():
			if debug {
				fmt.Printf("DEBUG: Context cancelled, exiting\n")
			}
			return
		}
	}
}
