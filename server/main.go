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

// State represents the overall state of the system
type State struct {
	OverallState         string `json:"overallState"`
	DBState              string `json:"dbState"`
	FSState              string `json:"fsState"`
	ProcessState         string `json:"processState"`
	ProcessExitCode      int    `json:"processExitCode"`
	CheckpointInProgress bool   `json:"checkpointInProgress"`
	RestoreInProgress    bool   `json:"restoreInProgress"`
	ErrorType            string `json:"errorType"`
	RestartAttempt       int    `json:"restartAttempt"`
	RestartDelay         int    `json:"restartDelay"`
	ShutdownInProgress   bool   `json:"shutdownInProgress"`
	ExitRequested        bool   `json:"exitRequested"`
	SignalReceived       string `json:"signalReceived"`
	DBShutdownTimeout    int    `json:"dbShutdownTimeout"`
	FSShutdownTimeout    int    `json:"fsShutdownTimeout"`
	DBForceKilled        bool   `json:"dbForceKilled"`
	FSForceKilled        bool   `json:"fsForceKilled"`
}

// StateChange represents a state transition for tracing
type StateChange struct {
	Timestamp time.Time `json:"timestamp"`
	From      State     `json:"from"`
	To        State     `json:"to"`
	Reason    string    `json:"reason"`
}

// SpriteEnv represents the main environment
type SpriteEnv struct {
	state             State
	stateChanges      []StateChange
	ctx               context.Context
	cancel            context.CancelFunc
	componentSet      *ComponentSet
	supervisedProcess *ProcessManager
	debug             bool
}

// NewSpriteEnv creates a new SpriteEnv instance
func NewSpriteEnv() *SpriteEnv {
	ctx, cancel := context.WithCancel(context.Background())
	return &SpriteEnv{
		state: State{
			OverallState:         StateInitializing,
			DBState:              StateInitializing,
			FSState:              StateInitializing,
			ProcessState:         ProcessStopped,
			ProcessExitCode:      0,
			CheckpointInProgress: false,
			RestoreInProgress:    false,
			ErrorType:            ErrorNone,
			RestartAttempt:       0,
			RestartDelay:         0,
			ShutdownInProgress:   false,
			ExitRequested:        false,
			SignalReceived:       SignalNone,
			DBShutdownTimeout:    0,
			FSShutdownTimeout:    0,
			DBForceKilled:        false,
			FSForceKilled:        false,
		},
		ctx:    ctx,
		cancel: cancel,
	}
}

// SetComponentSet sets the component set to be managed
func (s *SpriteEnv) SetComponentSet(cs *ComponentSet) {
	s.componentSet = cs
}

// SetSupervisedProcess sets the supervised process to be managed
func (s *SpriteEnv) SetSupervisedProcess(proc *ProcessManager) {
	s.supervisedProcess = proc
}

// updateState updates the environment state based on component states
func (s *SpriteEnv) updateState() {
	oldState := s.state

	// Update component states from ComponentSet
	if s.componentSet != nil {
		componentStates := s.componentSet.GetState()
		if dbState, exists := componentStates["DB"]; exists {
			s.state.DBState = dbState
		}
		if fsState, exists := componentStates["FS"]; exists {
			s.state.FSState = fsState
		}
	}

	// Update process state from SupervisedProcess
	if s.supervisedProcess != nil {
		s.state.ProcessState = s.supervisedProcess.GetState()
	}

	// Determine error type according to TLA+ spec
	s.state.ErrorType = s.determineErrorType()

	// Update overall state according to TLA+ spec
	if s.state.ErrorType != ErrorNone {
		s.state.OverallState = StateError
	} else if s.state.DBState == StateInitializing || s.state.FSState == StateInitializing {
		s.state.OverallState = StateInitializing
	} else if s.state.CheckpointInProgress {
		s.state.OverallState = StateCheckpointing
	} else if s.state.RestoreInProgress {
		s.state.OverallState = StateRestoring
	} else if s.state.DBState == StateRunning && s.state.FSState == StateRunning && s.state.ProcessState == ProcessRunning {
		s.state.OverallState = StateRunning
	} else if s.state.ShutdownInProgress {
		s.state.OverallState = StateShutdown
	}

	// Record state change if needed
	if oldState != s.state {
		s.recordStateChange(oldState, s.state, "State updated from component states")
	}
}

// determineErrorType implements the DetermineErrorType logic from the TLA+ spec
func (s *SpriteEnv) determineErrorType() string {
	if s.state.DBState == StateError {
		return ErrorDBError
	}
	if s.state.FSState == StateError {
		return ErrorFSError
	}
	if s.state.ProcessState == ProcessError {
		return ErrorProcessError
	}
	if s.state.ProcessState == ProcessCrashed {
		return ErrorProcessCrash
	}
	if s.state.ProcessState == ProcessKilled {
		return ErrorProcessKilled
	}
	if s.state.CheckpointInProgress && (s.state.DBState == StateError || s.state.FSState == StateError) {
		return ErrorCheckpointError
	}
	if s.state.RestoreInProgress && (s.state.DBState == StateError || s.state.FSState == StateError) {
		return ErrorRestoreError
	}
	if s.state.DBState == StateInitializing || s.state.FSState == StateInitializing {
		return ErrorStartupError
	}
	return ErrorNone
}

// handleSignal implements signal handling according to TLA+ spec
func (s *SpriteEnv) handleSignal(sig os.Signal) {
	// Don't use mutex in signal handler - keep it fast and non-blocking

	if s.debug {
		log.Printf("DEBUG: Signal handler received: %v", sig)
	}

	// Stop ComponentSet and SupervisedProcess
	if s.componentSet != nil {
		s.componentSet.Stop()
	}
	if s.supervisedProcess != nil {
		s.supervisedProcess.Stop()
	}
}

// StartCheckpoint implements checkpoint operation according to TLA+ spec
func (s *SpriteEnv) StartCheckpoint() error {
	if s.state.CheckpointInProgress || s.state.RestoreInProgress {
		return fmt.Errorf("operation already in progress")
	}

	oldState := s.state
	s.state.CheckpointInProgress = true
	s.recordStateChange(oldState, s.state, "Starting checkpoint")

	return nil
}

// StartRestore implements restore operation according to TLA+ spec
func (s *SpriteEnv) StartRestore() error {
	if s.state.CheckpointInProgress || s.state.RestoreInProgress {
		return fmt.Errorf("operation already in progress")
	}

	oldState := s.state
	s.state.RestoreInProgress = true
	s.recordStateChange(oldState, s.state, "Starting restore")

	return nil
}

// recordStateChange records a state transition for tracing
func (s *SpriteEnv) recordStateChange(from, to State, reason string) {
	change := StateChange{
		Timestamp: time.Now(),
		From:      from,
		To:        to,
		Reason:    reason,
	}
	s.stateChanges = append(s.stateChanges, change)

	// Output TLA+ compatible trace
	vars := map[string]interface{}{
		"overallState":         to.OverallState,
		"dbState":              to.DBState,
		"fsState":              to.FSState,
		"processState":         to.ProcessState,
		"processExitCode":      to.ProcessExitCode,
		"checkpointInProgress": to.CheckpointInProgress,
		"restoreInProgress":    to.RestoreInProgress,
		"errorType":            to.ErrorType,
		"restartAttempt":       to.RestartAttempt,
		"restartDelay":         to.RestartDelay,
		"shutdownInProgress":   to.ShutdownInProgress,
		"exitRequested":        to.ExitRequested,
		"signalReceived":       to.SignalReceived,
		"dbShutdownTimeout":    to.DBShutdownTimeout,
		"fsShutdownTimeout":    to.FSShutdownTimeout,
		"dbForceKilled":        to.DBForceKilled,
		"fsForceKilled":        to.FSForceKilled,
	}

	trace := map[string]interface{}{
		"vars": vars,
	}

	log.Printf("STATE_CHANGE: %s", toJSON(trace))
}

// toJSON converts a value to JSON string
func toJSON(v interface{}) string {
	b, err := json.Marshal(v)
	if err != nil {
		return fmt.Sprintf("{\"error\": \"%v\"}", err)
	}
	return string(b)
}

// nextRestartDelay implements the NextRestartDelay logic from the TLA+ spec
func (s *SpriteEnv) nextRestartDelay() int {
	if s.state.RestartAttempt == 0 {
		return 1
	}
	// Simplified version - in real implementation would use proper random with jitter
	nextDelay := s.state.RestartDelay*2 + 3
	if nextDelay > 60 {
		return 60
	}
	return nextDelay
}

func main() {
	// Parse command line arguments
	var testDir string
	var debug bool
	flag.StringVar(&testDir, "test-dir", "", "Directory containing test scripts")
	flag.BoolVar(&debug, "debug", false, "Enable debug logging")
	flag.Parse()

	// Get supervised process path from remaining arguments after --
	var supervisedProcessPath string
	args := flag.Args()
	if len(args) > 0 {
		supervisedProcessPath = args[0]
	}

	if testDir != "" && supervisedProcessPath == "" {
		log.Printf("ERROR: When using -test-dir, supervised process path must be provided after --")
		log.Printf("Usage: %s -test-dir <dir> -debug -- <supervised-process-path>", os.Args[0])
		os.Exit(1)
	}

	env := NewSpriteEnv()
	env.debug = debug

	// Set up signal handling
	sigChan := make(chan os.Signal, 1)
	signal.Notify(sigChan, syscall.SIGTERM, syscall.SIGINT)

	// Start HTTP server for state inspection
	go func() {
		http.HandleFunc("/state", func(w http.ResponseWriter, r *http.Request) {
			json.NewEncoder(w).Encode(env.state)
		})

		http.HandleFunc("/trace", func(w http.ResponseWriter, r *http.Request) {
			json.NewEncoder(w).Encode(env.stateChanges)
		})

		log.Fatal(http.ListenAndServe(":8080", nil))
	}()

	// Initialize components if test directory is provided
	if testDir != "" {
		if debug {
			log.Printf("DEBUG: Using test scripts from %s", testDir)
			log.Printf("DEBUG: Using supervised process: %s", supervisedProcessPath)
		}

		// Create ComponentSet for storage components
		componentSet := NewComponentSet(debug)

		// Create individual components
		dbManager := NewComponentManager(env, "DB", filepath.Join(testDir, "db", "start.sh"), filepath.Join(testDir, "db", "ready.sh"))
		fsManager := NewComponentManager(env, "FS", filepath.Join(testDir, "fs", "start.sh"), filepath.Join(testDir, "fs", "ready.sh"))

		// Add components to the set
		componentSet.AddComponent("DB", dbManager)
		componentSet.AddComponent("FS", fsManager)

		// Create supervised process with provided path
		supervisedProcess := NewProcessManager(env, supervisedProcessPath, "")

		// Set up environment
		env.SetComponentSet(componentSet)
		env.SetSupervisedProcess(supervisedProcess)

		// Start ComponentSet first
		if err := componentSet.Start(); err != nil {
			log.Printf("Failed to start component set: %v", err)
			os.Exit(1)
		}

		if debug {
			log.Printf("DEBUG: ComponentSet started, waiting for components to be ready")
		}

		// Wait for all components to be ready before starting supervised process (per TLA+ spec)
		go func() {
			for {
				if componentSet.GetOverallState() == StateRunning {
					if debug {
						log.Printf("DEBUG: All components ready, starting supervised process")
					}
					if err := supervisedProcess.Start(); err != nil {
						log.Printf("Failed to start supervised process: %v", err)
						os.Exit(1)
					}
					break
				}
				time.Sleep(100 * time.Millisecond)
			}
		}()

		if debug {
			log.Printf("DEBUG: ComponentSet started, supervised process will start when components are ready")
		}
	}

	// Main event loop
	ticker := time.NewTicker(100 * time.Millisecond)
	defer ticker.Stop()

	shutdownTimer := time.NewTimer(30 * time.Second) // Give 30 seconds for graceful shutdown
	shutdownTimer.Stop()                             // Don't start until we get a signal

	for {
		select {
		case sig := <-sigChan:
			if debug {
				log.Printf("DEBUG: Received signal: %v", sig)
			}

			// Set shutdown flag for graceful signals
			if sig == syscall.SIGTERM || sig == syscall.SIGINT {
				env.state.ShutdownInProgress = true
				env.state.SignalReceived = SignalGraceful
			}

			// Handle signals according to spec
			env.handleSignal(sig)

			// Start shutdown timer for graceful signals
			if sig == syscall.SIGTERM || sig == syscall.SIGINT {
				if debug {
					log.Printf("DEBUG: Starting graceful shutdown, will force exit in 30 seconds")
				}
				shutdownTimer.Reset(30 * time.Second)
			}

		case <-shutdownTimer.C:
			if debug {
				log.Printf("DEBUG: Shutdown timeout exceeded, forcing exit")
			}
			os.Exit(1)

		case <-env.ctx.Done():
			if debug {
				log.Printf("DEBUG: Context cancelled, exiting")
			}
			return

		case <-ticker.C:
			// Update environment state based on component states
			env.updateState()

			// Handle shutdown timeouts according to TLA+ spec
			if env.state.ShutdownInProgress {
				// Decrement timeouts if not zero
				if env.state.DBShutdownTimeout > 0 {
					env.state.DBShutdownTimeout--
				}
				if env.state.FSShutdownTimeout > 0 {
					env.state.FSShutdownTimeout--
				}

				// Force kill DB if timeout expires
				if env.state.DBShutdownTimeout == 0 && !env.state.DBForceKilled {
					env.state.DBForceKilled = true
					env.state.DBState = StateError
				}

				// Force kill FS if timeout expires
				if env.state.FSShutdownTimeout == 0 && !env.state.FSForceKilled {
					env.state.FSForceKilled = true
					env.state.FSState = StateError
				}

				// Exit if all components are stopped/killed after shutdown
				if (env.state.DBState == StateError || env.state.DBState == StateShutdown) &&
					(env.state.FSState == StateError || env.state.FSState == StateShutdown) &&
					(env.state.ProcessState == ProcessStopped || env.state.ProcessState == ProcessExited || env.state.ProcessState == ProcessKilled) {
					if debug {
						log.Printf("DEBUG: All components shut down, exiting gracefully")
					}
					os.Exit(0)
				}
			}
		}
	}
}
