package state

import (
	"context"
	"os"
	"syscall"

	"sprite-env/lib/adapters"

	"github.com/qmuntal/stateless"
)

// ProcessInterface defines what we need from a process
type ProcessInterface interface {
	Start(ctx context.Context) error
	Stop()
	Signal(sig os.Signal)
	// SetEventHandlers sets up Observer pattern callbacks (new approach)
	SetEventHandlers(handlers adapters.ProcessEventHandlers)
}

// ProcessStateType represents the states from the TLA+ spec
type ProcessStateType string

const (
	// Transition states
	ProcessStateInitializing ProcessStateType = "Initializing"
	ProcessStateStarting     ProcessStateType = "Starting"
	ProcessStateStopping     ProcessStateType = "Stopping"
	ProcessStateSignaling    ProcessStateType = "Signaling"

	// Final states
	ProcessStateStopped ProcessStateType = "Stopped"
	ProcessStateExited  ProcessStateType = "Exited"
	ProcessStateCrashed ProcessStateType = "Crashed"
	ProcessStateKilled  ProcessStateType = "Killed"

	// Active states
	ProcessStateRunning ProcessStateType = "Running"

	// Error states
	ProcessStateError ProcessStateType = "Error"
)

// ProcessTrigger represents the triggers that cause state transitions
type ProcessTrigger string

const (
	TriggerStart   ProcessTrigger = "Start"
	TriggerStarted ProcessTrigger = "Started"
	TriggerStop    ProcessTrigger = "Stop"
	TriggerStopped ProcessTrigger = "Stopped"
	TriggerSignal  ProcessTrigger = "Signal"
	TriggerExited  ProcessTrigger = "Exited"
	TriggerCrashed ProcessTrigger = "Crashed"
	TriggerKilled  ProcessTrigger = "Killed"
	TriggerFailed  ProcessTrigger = "Failed"
	TriggerRestart ProcessTrigger = "Restart"
)

// ProcessState manages the state of a supervised process
type ProcessState struct {
	*stateless.StateMachine
	process    ProcessInterface
	lastSignal os.Signal
	ctx        context.Context
	cancel     context.CancelFunc
}

// NewProcessState creates a new process state machine with a real process
func NewProcessState(config adapters.ProcessConfig) *ProcessState {
	return NewProcessStateWithProcess(adapters.NewProcess(config))
}

// NewProcessStateWithProcess creates a new process state machine with a custom process implementation
func NewProcessStateWithProcess(process ProcessInterface) *ProcessState {
	psm := &ProcessState{
		process: process,
	}

	// Create the state machine
	psm.StateMachine = stateless.NewStateMachine(ProcessStateInitializing)

	// Configure state transitions based on TLA+ spec
	psm.configureStateMachine()

	// Set up our internal event handlers with the process immediately
	// This ensures handlers are registered before the process starts emitting events
	psm.setupEventHandlers()

	return psm
}

// cleanup handles cleanup when entering final states
func (psm *ProcessState) cleanup(ctx context.Context, args ...any) error {
	if psm.cancel != nil {
		psm.cancel()
	}
	return nil
}

// configureStateMachine sets up the state machine transitions according to TLA+ spec
func (psm *ProcessState) configureStateMachine() {
	// From Initializing
	psm.Configure(ProcessStateInitializing).
		Permit(TriggerStart, ProcessStateStarting).
		Permit(TriggerFailed, ProcessStateError)

	// From Starting
	psm.Configure(ProcessStateStarting).
		Permit(TriggerStarted, ProcessStateRunning).
		Permit(TriggerStop, ProcessStateStopping).    // Allow stopping during startup
		Permit(TriggerSignal, ProcessStateSignaling). // Allow killing during startup
		Permit(TriggerFailed, ProcessStateError).
		OnEntry(func(ctx context.Context, args ...any) error {
			// Set up context for process lifecycle
			psm.ctx, psm.cancel = context.WithCancel(ctx)

			// Start the process (our handlers are already registered)
			_ = psm.process.Start(psm.ctx)
			return nil
		})

	// From Running
	psm.Configure(ProcessStateRunning).
		Permit(TriggerStop, ProcessStateStopping).
		Permit(TriggerSignal, ProcessStateSignaling).
		Permit(TriggerExited, ProcessStateExited).
		Permit(TriggerCrashed, ProcessStateCrashed).
		Permit(TriggerKilled, ProcessStateKilled).
		Permit(TriggerFailed, ProcessStateError)

	// From Stopping
	psm.Configure(ProcessStateStopping).
		Permit(TriggerStopped, ProcessStateStopped).
		Permit(TriggerSignal, ProcessStateSignaling). // Allow escalating to kill during stop
		Permit(TriggerFailed, ProcessStateError).
		PermitReentry(TriggerStop). // Allow multiple stop calls
		OnEntry(func(ctx context.Context, args ...any) error {
			// Actually stop the process when entering Stopping state
			psm.process.Stop()
			return nil
		})

	// From Signaling
	psm.Configure(ProcessStateSignaling).
		Permit(TriggerKilled, ProcessStateKilled).
		Permit(TriggerStopped, ProcessStateStopped).
		Permit(TriggerFailed, ProcessStateError).
		PermitReentry(TriggerSignal). // Allow multiple signal calls
		OnEntry(func(ctx context.Context, args ...any) error {
			// Actually signal the process when entering Signaling state
			psm.lastSignal = syscall.SIGKILL
			psm.process.Signal(syscall.SIGKILL)
			return nil
		})

	// From non-final states - allow restart
	psm.Configure(ProcessStateExited).
		Permit(TriggerRestart, ProcessStateStarting)

	psm.Configure(ProcessStateCrashed).
		Permit(TriggerRestart, ProcessStateStarting)

	// Final states have no outgoing transitions and need cleanup:
	// ProcessStateStopped, ProcessStateKilled, ProcessStateError are final
	psm.Configure(ProcessStateStopped).OnEntry(psm.cleanup)
	psm.Configure(ProcessStateKilled).OnEntry(psm.cleanup)
	psm.Configure(ProcessStateError).OnEntry(psm.cleanup)
}

// Fire wraps the stateless.StateMachine.Fire method
func (psm *ProcessState) Fire(trigger ProcessTrigger, args ...any) error {
	return psm.StateMachine.Fire(trigger, args...)
}

// setupEventHandlers sets up Observer pattern callbacks that trigger state transitions
func (psm *ProcessState) setupEventHandlers() {
	handlers := adapters.ProcessEventHandlers{
		Starting: func() {
			// Process is already starting, no trigger needed
		},
		Started: func() {
			// EmitEvent already runs in goroutine, so no need for another one
			psm.Fire(TriggerStarted)
		},
		Stopping: func() {
			// Process is already stopping, no trigger needed
		},
		Stopped: func() {
			// EmitEvent already runs in goroutine, so no need for another one
			psm.Fire(TriggerStopped)
		},
		Signaled: func(sig os.Signal) {
			// EmitEvent already runs in goroutine, so no need for another one
			psm.lastSignal = sig
			// Determine if this is a terminating signal
			if sig == syscall.SIGKILL {
				psm.Fire(TriggerKilled)
			}
			// Non-terminating signals don't trigger state changes
		},
		Exited: func() {
			// EmitEvent already runs in goroutine, so no need for another one
			psm.Fire(TriggerCrashed)
		},
		Restarting: func() {
			// EmitEvent already runs in goroutine, so no need for another one
			psm.Fire(TriggerRestart)
		},
		Failed: func(err error) {
			// EmitEvent already runs in goroutine, so no need for another one
			psm.Fire(TriggerFailed)
		},
	}

	psm.process.SetEventHandlers(handlers)
}

// AddStateChangeCallback adds a callback that will be called on process state changes
func (psm *ProcessState) AddStateChangeCallback(callback func(stateless.Transition)) {
	psm.OnTransitioned(func(ctx context.Context, transition stateless.Transition) {
		callback(transition)
	})
}

func (psm *ProcessState) GetState() ProcessStateType {
	return ProcessStateType(psm.MustState().(ProcessStateType))
}
