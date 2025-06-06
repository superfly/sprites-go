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

	"sprite-env/server/lib"
	"sprite-env/server/lib/states"
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
	globalStateManager  *states.GlobalStateManager
	componentSetManager *states.ComponentSetStateManager
	componentSet        *lib.ComponentSet
	supervisedProcess   *lib.ProcessManager
	ctx                 context.Context
	cancel              context.CancelFunc
	debug               bool
	tlaTrace            bool
}

// NewSpriteEnv creates a new SpriteEnv instance
func NewSpriteEnv() *SpriteEnv {
	ctx, cancel := context.WithCancel(context.Background())

	// Create state managers
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

	return &SpriteEnv{
		globalStateManager:  globalStateManager,
		componentSetManager: componentSetManager,
		ctx:                 ctx,
		cancel:              cancel,
	}
}

// SetComponentSet sets the component set to be managed
func (s *SpriteEnv) SetComponentSet(cs *lib.ComponentSet) {
	s.componentSet = cs
}

// SetSupervisedProcess sets the supervised process to be managed
func (s *SpriteEnv) SetSupervisedProcess(proc *lib.ProcessManager) {
	s.supervisedProcess = proc
}

// updateState updates the environment state based on component states
func (s *SpriteEnv) updateState() {
	// Get current states from actual components
	var dbState, fsState, processState string
	var componentSetOverallState string

	if s.componentSet != nil {
		componentStates := s.componentSet.GetState()
		componentSetOverallState = s.componentSet.GetOverallState()

		// Update component states in state manager
		if dbStateVal, exists := componentStates["DB"]; exists {
			dbState = dbStateVal
			s.componentSetManager.AddComponent("DB", &states.ComponentState{State: dbState})
		}
		if fsStateVal, exists := componentStates["FS"]; exists {
			fsState = fsStateVal
			s.componentSetManager.AddComponent("FS", &states.ComponentState{State: fsState})
		}
	}

	// Update process state from SupervisedProcess
	if s.supervisedProcess != nil {
		processState = s.supervisedProcess.GetState()
		s.globalStateManager.State.ProcessState = processState
	}

	// Calculate overall state according to TLA+ spec
	errorType := s.determineErrorType()
	s.globalStateManager.State.ErrorType = errorType

	var overallState string
	if errorType != ErrorNone {
		overallState = StateError
	} else if dbState == StateInitializing || fsState == StateInitializing || processState == ProcessStarting {
		overallState = StateInitializing
	} else if s.globalStateManager.State.CheckpointInProgress {
		overallState = StateCheckpointing
	} else if s.globalStateManager.State.RestoreInProgress {
		overallState = StateRestoring
	} else if dbState == StateRunning && fsState == StateRunning && processState == ProcessRunning {
		overallState = StateRunning
	} else if s.globalStateManager.State.ShutdownInProgress {
		overallState = StateShutdown
	} else {
		overallState = StateInitializing
	}

	s.globalStateManager.State.State = overallState

	// Update component set state
	s.componentSetManager.State.State = componentSetOverallState
	if componentSetOverallState == StateError {
		s.componentSetManager.State.ErrorType = errorType
	} else {
		s.componentSetManager.State.ErrorType = states.ErrorNone
	}

	// Record the state change via centralized tracing
	s.globalStateManager.RecordStateChange("State updated from component states")
}

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
		processState := s.supervisedProcess.GetState()
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

// handleSignal implements signal handling according to TLA+ spec
func (s *SpriteEnv) handleSignal(sig os.Signal) {
	if s.debug {
		fmt.Printf("DEBUG: Signal handler received: %v\n", sig)
	}

	// Forward signal to supervised process ONLY
	// Components will be stopped after supervised process exits
	if s.supervisedProcess != nil {
		s.supervisedProcess.Stop()
	}
}

// StartCheckpoint implements checkpoint operation according to TLA+ spec
func (s *SpriteEnv) StartCheckpoint() error {
	state := s.globalStateManager.State
	if state.CheckpointInProgress || state.RestoreInProgress {
		return fmt.Errorf("operation already in progress")
	}

	s.globalStateManager.State.CheckpointInProgress = true
	s.globalStateManager.RecordStateChange("Starting checkpoint")
	return nil
}

// StartRestore implements restore operation according to TLA+ spec
func (s *SpriteEnv) StartRestore() error {
	state := s.globalStateManager.State
	if state.CheckpointInProgress || state.RestoreInProgress {
		return fmt.Errorf("operation already in progress")
	}

	s.globalStateManager.State.RestoreInProgress = true
	s.globalStateManager.RecordStateChange("Starting restore")
	return nil
}

// UpdateComponentState updates a single component's state and records the change
func (s *SpriteEnv) UpdateComponentState(component string, newState string, oldState string) {
	// Update the existing component's state
	if componentState, exists := s.componentSetManager.State.Components[component]; exists {
		componentState.UpdateState(newState)
		// Trigger state change notification
		s.componentSetManager.UpdateState(component + " state changed from " + oldState + " to " + newState)
	}

	if s.debug {
		fmt.Printf("DEBUG: %s state changed from %s to %s\n", component, oldState, newState)
	}
}

// UpdateProcessState updates the process state and records the change
func (s *SpriteEnv) UpdateProcessState(newState string, oldState string) {
	s.globalStateManager.State.ProcessState = newState

	// Trigger overall state recalculation with current component set state
	if s.componentSetManager != nil {
		s.globalStateManager.UpdateState(s.componentSetManager.State, "Process state changed from "+oldState+" to "+newState)
	} else {
		// If no component set manager, just emit trace
		s.globalStateManager.RecordStateChange("Process state changed from " + oldState + " to " + newState)
	}

	if s.debug {
		fmt.Printf("DEBUG: Process state changed from %s to %s\n", oldState, newState)
	}
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

	// Set up signal handling
	sigChan := make(chan os.Signal, 1)
	signal.Notify(sigChan, syscall.SIGTERM, syscall.SIGINT)

	// Start HTTP server for state inspection
	go func() {
		http.HandleFunc("/state", func(w http.ResponseWriter, r *http.Request) {
			json.NewEncoder(w).Encode(env.globalStateManager.State)
		})

		http.HandleFunc("/trace", func(w http.ResponseWriter, r *http.Request) {
			json.NewEncoder(w).Encode(env.globalStateManager.Changes)
		})

		log.Fatal(http.ListenAndServe(":8080", nil))
	}()

	// Initialize components if test directory is provided
	if testDir != "" {
		if debug {
			fmt.Printf("DEBUG: Using test scripts from %s\n", testDir)
			fmt.Printf("DEBUG: Using supervised process: %s\n", supervisedProcessPath)
		}

		// Create ComponentSet for storage components
		componentSet := lib.NewComponentSet(debug)

		// Create individual components
		dbManager := lib.NewComponentManager(env, debug, "DB", filepath.Join(testDir, "db", "start.sh"), filepath.Join(testDir, "db", "ready.sh"))
		fsManager := lib.NewComponentManager(env, debug, "FS", filepath.Join(testDir, "fs", "start.sh"), filepath.Join(testDir, "fs", "ready.sh"))

		// Add components to the set
		componentSet.AddComponent("DB", dbManager)
		componentSet.AddComponent("FS", fsManager)

		// Create supervised process with provided path
		supervisedProcess := lib.NewProcessManager(env, debug, supervisedProcessPath, "")

		// Set up environment
		env.SetComponentSet(componentSet)
		env.SetSupervisedProcess(supervisedProcess)

		// Start ComponentSet first
		if err := componentSet.Start(); err != nil {
			log.Printf("Failed to start component set: %v", err)
			exitCode = 1
			return
		}

		if debug {
			fmt.Printf("DEBUG: ComponentSet started, waiting for components to be ready\n")
		}

		// Wait for all components to be ready before starting supervised process (per TLA+ spec)
		go func() {
			for {
				if componentSet.GetOverallState() == StateRunning {
					if debug {
						fmt.Printf("DEBUG: All components ready, starting supervised process\n")
					}
					if err := supervisedProcess.Start(); err != nil {
						log.Printf("Failed to start supervised process: %v", err)
						exitCode = 1
						env.cancel() // Signal main loop to exit
						return
					}
					break
				}
				time.Sleep(100 * time.Millisecond)
			}
		}()

		if debug {
			fmt.Printf("DEBUG: ComponentSet started, supervised process will start when components are ready\n")
		}
	}

	// Main event loop
	ticker := time.NewTicker(100 * time.Millisecond)
	defer ticker.Stop()

	shutdownTimer := time.NewTimer(30 * time.Second) // Give 30 seconds for graceful shutdown
	shutdownTimer.Stop()                             // Don't start until we get a signal

	var componentsShutdownInitiated bool // Track if we've started component shutdown

	for {
		select {
		case sig := <-sigChan:
			if debug {
				fmt.Printf("DEBUG: Received signal: %v\n", sig)
			}

			// Set shutdown flag for graceful signals
			if sig == syscall.SIGTERM || sig == syscall.SIGINT {
				env.globalStateManager.State.ShutdownInProgress = true
				env.globalStateManager.State.SignalReceived = SignalGraceful

				// Set exit code based on signal (Unix convention: 128 + signal number)
				if sig == syscall.SIGTERM {
					exitCode = 128 + 15 // 143
				} else if sig == syscall.SIGINT {
					exitCode = 128 + 2 // 130
				}
			}

			// Handle signals according to spec
			env.handleSignal(sig)

			// Start shutdown timer for graceful signals
			if sig == syscall.SIGTERM || sig == syscall.SIGINT {
				if debug {
					fmt.Printf("DEBUG: Starting graceful shutdown, will force exit in 30 seconds\n")
				}
				shutdownTimer.Reset(30 * time.Second)
			}

		case <-shutdownTimer.C:
			if debug {
				fmt.Printf("DEBUG: Shutdown timeout exceeded, exiting\n")
			}
			exitCode = 1 // Failed shutdown
			return

		case <-env.ctx.Done():
			if debug {
				fmt.Printf("DEBUG: Context cancelled, exiting\n")
			}
			return

		case <-ticker.C:
			// Check if supervised process has stopped and we need to stop components
			if env.globalStateManager.State.ShutdownInProgress && !componentsShutdownInitiated {
				var processState string
				if env.supervisedProcess != nil {
					processState = env.supervisedProcess.GetState()
				}

				// If supervised process has stopped, now stop components
				if processState == ProcessStopped || processState == ProcessExited ||
					processState == ProcessKilled || processState == ProcessCrashed || processState == ProcessError {
					if debug {
						fmt.Printf("DEBUG: Supervised process stopped (%s), now stopping components\n", processState)
					}
					if env.componentSet != nil {
						env.componentSet.Stop()
					}
					componentsShutdownInitiated = true
				}
			}

			// Handle shutdown timeouts according to TLA+ spec
			state := env.globalStateManager.State
			if state.ShutdownInProgress {
				// Decrement timeouts if not zero
				if state.DBShutdownTimeout > 0 {
					state.DBShutdownTimeout--
				}
				if state.FSShutdownTimeout > 0 {
					state.FSShutdownTimeout--
				}

				// Force kill DB if timeout expires
				if state.DBShutdownTimeout == 0 && !state.DBForceKilled {
					state.DBForceKilled = true
					env.UpdateComponentState("DB", StateError, "Running")
				}

				// Force kill FS if timeout expires
				if state.FSShutdownTimeout == 0 && !state.FSForceKilled {
					state.FSForceKilled = true
					env.UpdateComponentState("FS", StateError, "Running")
				}

				// Exit if all components are stopped/killed after shutdown
				componentStates := make(map[string]string)
				if env.componentSet != nil {
					componentStates = env.componentSet.GetState()
				}

				dbStopped := false
				fsStopped := false
				if dbState, exists := componentStates["DB"]; exists {
					dbStopped = (dbState == StateError || dbState == StateShutdown)
				}
				if fsState, exists := componentStates["FS"]; exists {
					fsStopped = (fsState == StateError || fsState == StateShutdown)
				}

				processStopped := false
				if env.supervisedProcess != nil {
					processState := env.supervisedProcess.GetState()
					// Only consider truly final states, not intermediate states
					processStopped = (processState == ProcessStopped || processState == ProcessExited || processState == ProcessKilled || processState == ProcessCrashed || processState == ProcessError)
				}

				if dbStopped && fsStopped && processStopped {
					if debug {
						fmt.Printf("DEBUG: All components shut down, exiting gracefully\n")
					}

					// Set exit code based on final state (only if not already set by signal)
					if exitCode == 0 && env.globalStateManager.State.ErrorType != ErrorNone {
						exitCode = 1
					}
					return
				}
			}
		}
	}
}
