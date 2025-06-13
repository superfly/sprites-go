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
	Start(ctx context.Context) <-chan adapters.EventType
	Stop()
	Signal(sig os.Signal)
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
	eventCh    <-chan adapters.EventType
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
			// Actually start the process when entering Starting state
			psm.ctx, psm.cancel = context.WithCancel(ctx)
			psm.eventCh = psm.process.Start(psm.ctx)
			go psm.watchEvents(psm.ctx, psm.eventCh)
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

// watchEvents watches for events from the process and updates state accordingly
func (psm *ProcessState) watchEvents(ctx context.Context, eventCh <-chan adapters.EventType) {
	for {
		select {
		case <-ctx.Done():
			return
		case event, ok := <-eventCh:
			if !ok {
				return // Channel closed
			}
			psm.handleEvent(event)
		}
	}
}

// handleEvent maps process events to state machine triggers
func (psm *ProcessState) handleEvent(event adapters.EventType) {
	var trigger ProcessTrigger

	switch event {
	case adapters.EventStarting:
		// Process is already starting, no trigger needed
		return
	case adapters.EventStarted:
		trigger = TriggerStarted
	case adapters.EventStopping:
		// Process is already stopping, no trigger needed
		return
	case adapters.EventStopped:
		trigger = TriggerStopped
	case adapters.EventSignaled:
		// Determine if this is a terminating signal
		if psm.lastSignal == syscall.SIGKILL {
			trigger = TriggerFailed
		} else {
			// Non-terminating signal - process should handle it gracefully
			return
		}
	case adapters.EventExited:
		// EventExited means the process will restart - this is a restartable crash
		trigger = TriggerCrashed
	case adapters.EventRestarting:
		trigger = TriggerRestart
	case adapters.EventFailed:
		// EventFailed means permanent failure
		trigger = TriggerFailed
	default:
		return // Unknown event
	}

	psm.Fire(trigger)
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
