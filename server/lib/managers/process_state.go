package managers

import (
	"context"
	"os"

	"github.com/qmuntal/stateless"
)

// ManagedProcess defines the interface for a process that can be managed
type ManagedProcess interface {
	Start(ctx context.Context) error
	Stop()
	Signal(sig os.Signal)
	GetState() string // Returns "stopped", "running", "error", "crashed", "killed", "exited"
}

// ProcessStateConfig holds the configuration for a process state manager
type ProcessStateConfig struct {
	InitialState string // Initial state, defaults to "Initializing"
	Process      ManagedProcess
}

// ProcessState is a purely declarative intent processor for process states
// Following cursor rules: extends stateless.StateMachine
type ProcessState struct {
	*stateless.StateMachine
	process ManagedProcess
}

// Fire overrides the base Fire method
func (psm *ProcessState) Fire(trigger string, args ...any) error {
	err := psm.StateMachine.Fire(trigger, args...)
	return err
}

// NewProcessState creates a new process state manager
// Initial state is "Initializing" as per spec (unless overridden in config)
func NewProcessState(config ProcessStateConfig) *ProcessState {
	initialState := config.InitialState
	if initialState == "" {
		initialState = "Initializing" // Default per spec
	}

	sm := stateless.NewStateMachine(initialState)

	psm := &ProcessState{
		StateMachine: sm,
		process:      config.Process,
	}

	// Configure states based on ProcessTransition definition

	// Initializing - process not yet started
	sm.Configure("Initializing").
		Permit("Starting", "Starting").
		Permit("ProcessError", "Error")

	// Starting - process is being started
	sm.Configure("Starting").
		Permit("ProcessRunning", "Running").
		Permit("ProcessError", "Error").
		OnEntry(psm.handleStarting)

	// Running - process is active and running
	sm.Configure("Running").
		Permit("Stopping", "Stopping").
		Permit("ProcessError", "Error").
		Permit("ProcessCrashed", "Crashed").
		Permit("ProcessKilled", "Killed").
		Permit("ProcessExited", "Exited")

	// Stopping - process is being stopped gracefully
	sm.Configure("Stopping").
		Permit("ProcessStopped", "Stopped").
		Permit("ProcessError", "Error").
		OnEntry(psm.handleStopping)

	// Terminal states - no transitions out
	sm.Configure("Stopped") // Process stopped gracefully
	sm.Configure("Error")   // Process failed with error
	sm.Configure("Crashed") // Process crashed unexpectedly
	sm.Configure("Killed")  // Process was forcefully killed
	sm.Configure("Exited")  // Process exited on its own

	return psm
}

// handleStarting is called when entering Starting state
func (psm *ProcessState) handleStarting(ctx context.Context, args ...any) error {
	if psm.process != nil {
		// Start the process
		if err := psm.process.Start(ctx); err != nil {
			// Transition to Error state on failure
			psm.Fire("ProcessError")
			return err
		}

		// For managed processes, we rely on status updates to transition to Running
		if psm.process.GetState() == "running" {
			psm.Fire("ProcessRunning")
		}
	}
	return nil
}

// handleStopping is called when entering Stopping state
func (psm *ProcessState) handleStopping(ctx context.Context, args ...any) error {
	if psm.process != nil {
		// Stop the process gracefully
		psm.process.Stop()

		// For managed processes, we rely on status updates to transition to Stopped
		if psm.process.GetState() == "stopped" {
			psm.Fire("ProcessStopped")
		}
	}
	return nil
}

// SetSystemState sets a reference to the parent system state manager
// This is only used for constraint validation in TLA+ spec compliance
func (psm *ProcessState) SetSystemState(systemState interface{}) {
	// This method is kept for backwards compatibility but is now a no-op
}

// Close stops any background goroutines (none in this case)
func (psm *ProcessState) Close() {
	// No cleanup needed
}

// GetProcess returns the underlying managed process
func (psm *ProcessState) GetProcess() ManagedProcess {
	return psm.process
}
