package state

import (
	"context"
	"time"

	"sprite-env/lib/adapters"

	"github.com/qmuntal/stateless"
)

// ComponentInterface defines what we need from a component
type ComponentInterface interface {
	Start(ctx context.Context) error
	Stop()
	Checkpoint(ctx context.Context) error
	Restore(ctx context.Context) error
	// SetEventHandlers sets up Observer pattern callbacks (new approach)
	SetEventHandlers(handlers adapters.ComponentEventHandlers)
}

// ComponentStateType represents the states from the TLA+ spec
type ComponentStateType string

const (
	// Transition states
	ComponentStateInitializing  ComponentStateType = "Initializing"
	ComponentStateStarting      ComponentStateType = "Starting"
	ComponentStateStopping      ComponentStateType = "Stopping"
	ComponentStateRestoring     ComponentStateType = "Restoring"
	ComponentStateCheckpointing ComponentStateType = "Checkpointing"
	ComponentStateShuttingDown  ComponentStateType = "ShuttingDown"

	// Final states
	ComponentStateStopped  ComponentStateType = "Stopped"
	ComponentStateShutdown ComponentStateType = "Shutdown"

	// Active states
	ComponentStateRunning ComponentStateType = "Running"

	// Error states
	ComponentStateError ComponentStateType = "Error"
)

// ComponentTrigger represents the triggers that cause state transitions
type ComponentTrigger string

const (
	ComponentTriggerStart      ComponentTrigger = "Start"
	ComponentTriggerStarted    ComponentTrigger = "Started"
	ComponentTriggerReady      ComponentTrigger = "Ready"
	ComponentTriggerStop       ComponentTrigger = "Stop"
	ComponentTriggerStopped    ComponentTrigger = "Stopped"
	ComponentTriggerCheckpoint ComponentTrigger = "Checkpoint"
	ComponentTriggerRestore    ComponentTrigger = "Restore"
	ComponentTriggerShutdown   ComponentTrigger = "Shutdown"
	ComponentTriggerCompleted  ComponentTrigger = "Completed"
	ComponentTriggerFailed     ComponentTrigger = "Failed"
)

// ComponentState manages the state of a supervised component
type ComponentState struct {
	*stateless.StateMachine
	component ComponentInterface
	ctx       context.Context
	cancel    context.CancelFunc
}

// NewComponentState creates a new component state machine with a generic component
func NewComponentState(component ComponentInterface) *ComponentState {
	csm := &ComponentState{
		component: component,
	}

	// Create the state machine
	csm.StateMachine = stateless.NewStateMachine(ComponentStateInitializing)

	// Configure state transitions based on TLA+ spec
	csm.configureStateMachine()

	// Set up our internal event handlers with the component immediately
	// This ensures handlers are registered before the component starts emitting events
	csm.setupEventHandlers()

	// Activate the state machine to trigger OnEntry callbacks
	csm.Activate()

	return csm
}

// cleanup handles cleanup when entering final states
func (csm *ComponentState) cleanup(ctx context.Context, args ...any) error {
	if csm.cancel != nil {
		csm.cancel()
	}
	return nil
}

// startComponent starts the component (event handlers already registered in constructor)
func (csm *ComponentState) startComponent(ctx context.Context, args ...any) error {
	// Set up context for component lifecycle
	csm.ctx, csm.cancel = context.WithCancel(ctx)

	// Start the component (our handlers are already registered)
	err := csm.component.Start(csm.ctx)
	if err != nil {
		csm.Fire(ComponentTriggerFailed)
		return err
	}
	return nil
}

// performCheckpoint performs the checkpoint operation and signals completion
func (csm *ComponentState) performCheckpoint(ctx context.Context, args ...any) error {
	go func() {
		err := csm.component.Checkpoint(csm.ctx)
		if err != nil {
			csm.Fire(ComponentTriggerFailed)
			time.Sleep(time.Millisecond) // Ensure handler runs
		} else {
			csm.Fire(ComponentTriggerCompleted)
			time.Sleep(time.Millisecond) // Ensure handler runs
		}
	}()
	return nil
}

// performRestore performs the restore operation and signals completion
func (csm *ComponentState) performRestore(ctx context.Context, args ...any) error {
	go func() {
		err := csm.component.Restore(csm.ctx)
		if err != nil {
			csm.Fire(ComponentTriggerFailed)
			time.Sleep(time.Millisecond) // Ensure handler runs
		} else {
			csm.Fire(ComponentTriggerCompleted)
			time.Sleep(time.Millisecond) // Ensure handler runs
		}
	}()
	return nil
}

// configureStateMachine sets up the state machine transitions according to TLA+ spec
func (csm *ComponentState) configureStateMachine() {
	// From Initializing
	csm.Configure(ComponentStateInitializing).
		Permit(ComponentTriggerStart, ComponentStateStarting).
		Permit(ComponentTriggerFailed, ComponentStateError)

	// From Starting
	csm.Configure(ComponentStateStarting).
		OnEntry(csm.startComponent).
		Permit(ComponentTriggerStarted, ComponentStateRunning).
		Permit(ComponentTriggerStop, ComponentStateStopping).
		Permit(ComponentTriggerShutdown, ComponentStateShuttingDown).
		Permit(ComponentTriggerFailed, ComponentStateError)

	// From Running
	csm.Configure(ComponentStateRunning).
		Permit(ComponentTriggerStop, ComponentStateStopping).
		Permit(ComponentTriggerCheckpoint, ComponentStateCheckpointing).
		Permit(ComponentTriggerRestore, ComponentStateRestoring).
		Permit(ComponentTriggerShutdown, ComponentStateShuttingDown).
		Permit(ComponentTriggerFailed, ComponentStateError)

	// From Checkpointing (returns to Running)
	csm.Configure(ComponentStateCheckpointing).
		OnEntry(csm.performCheckpoint).
		Permit(ComponentTriggerCompleted, ComponentStateRunning).
		Permit(ComponentTriggerFailed, ComponentStateError)

	// From Restoring (goes to Starting after restore completes)
	csm.Configure(ComponentStateRestoring).
		OnEntry(csm.performRestore).
		Permit(ComponentTriggerCompleted, ComponentStateStarting).
		Permit(ComponentTriggerFailed, ComponentStateError)

	// From Stopping
	csm.Configure(ComponentStateStopping).
		Permit(ComponentTriggerStopped, ComponentStateStopped).
		Permit(ComponentTriggerShutdown, ComponentStateShuttingDown).
		Permit(ComponentTriggerFailed, ComponentStateError)

	// From ShuttingDown
	csm.Configure(ComponentStateShuttingDown).
		Permit(ComponentTriggerStopped, ComponentStateShutdown).
		Permit(ComponentTriggerFailed, ComponentStateError)

		// Final states (explicitly configured with no outgoing transitions)
	csm.Configure(ComponentStateStopped).OnEntry(csm.cleanup)
	csm.Configure(ComponentStateShutdown).OnEntry(csm.cleanup)
	csm.Configure(ComponentStateError).OnEntry(csm.cleanup)
}

// setupEventHandlers sets up Observer pattern callbacks that trigger state transitions
func (csm *ComponentState) setupEventHandlers() {
	handlers := adapters.ComponentEventHandlers{
		Starting: func() {
			// Component is starting, no trigger needed (already in Starting state)
		},
		Started: func() {
			csm.Fire(ComponentTriggerStarted)
		},
		Checking: func() {
			// Component is checking readiness, no state change needed
		},
		Ready: func() {
			csm.Fire(ComponentTriggerReady)
		},
		Stopping: func() {
			// Component is stopping, no trigger needed
		},
		Stopped: func() {
			// Determine the appropriate trigger based on current state
			currentState := csm.MustState()
			if currentState == ComponentStateShuttingDown {
				csm.Fire(ComponentTriggerStopped) // Will go to Shutdown state
			} else {
				csm.Fire(ComponentTriggerStopped) // Will go to Stopped state
			}
		},
		Failed: func(err error) {
			csm.Fire(ComponentTriggerFailed)
		},
	}

	csm.component.SetEventHandlers(handlers)
}
