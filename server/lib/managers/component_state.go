package managers

import (
	"context"
	"fmt"
	"sprite-env/lib/adapters"

	"github.com/qmuntal/stateless"
)

// ComponentEventType defines the type of event that can be emitted by components.
type ComponentEventType string

const (
	// ComponentStartingEvent is emitted when the component is about to be started.
	ComponentStartingEvent ComponentEventType = "starting"
	// ComponentStartedEvent is emitted when the component has successfully started.
	ComponentStartedEvent ComponentEventType = "started"
	// ComponentStoppingEvent is emitted when a stop sequence has been initiated.
	ComponentStoppingEvent ComponentEventType = "stopping"
	// ComponentStoppedEvent is emitted when the component has stopped.
	ComponentStoppedEvent ComponentEventType = "stopped"
	// ComponentCheckpointingEvent is emitted when checkpointing begins.
	ComponentCheckpointingEvent ComponentEventType = "checkpointing"
	// ComponentCheckpointedEvent is emitted when checkpointing completes.
	ComponentCheckpointedEvent ComponentEventType = "checkpointed"
	// ComponentRestoringEvent is emitted when restoring begins.
	ComponentRestoringEvent ComponentEventType = "restoring"
	// ComponentRestoredEvent is emitted when restoring completes.
	ComponentRestoredEvent ComponentEventType = "restored"
	// ComponentFailedEvent is emitted when the component has failed permanently.
	ComponentFailedEvent ComponentEventType = "failed"
)

// ManagedComponent defines the interface for components that can be managed by ComponentState
type ManagedComponent interface {
	GetName() string
	Start(ctx context.Context) error
	Stop()
	Checkpoint() error
	Restore() error
	Events() <-chan adapters.ComponentEventType
}

// ComponentState is a purely declarative intent processor for component states
// Following cursor rules: extends stateless.StateMachine
type ComponentState struct {
	*stateless.StateMachine
	component   ManagedComponent
	eventCtx    context.Context
	eventCancel context.CancelFunc
}

// NewComponentState creates a new component state manager with a managed component
// Initial state is "Initializing" as per TLA+ spec: Init == components = [i \in 1..N |-> "Initializing"]
// initialState parameter is optional - if empty, defaults to "Initializing"
func NewComponentState(name string, component ManagedComponent, monitors []StateMonitor, initialState ...string) *ComponentState {
	defaultState := "Initializing"
	if len(initialState) > 0 && initialState[0] != "" {
		defaultState = initialState[0]
	}
	sm := stateless.NewStateMachine(defaultState)

	eventCtx, eventCancel := context.WithCancel(context.Background())

	csm := &ComponentState{
		StateMachine: sm,
		component:    component,
		eventCtx:     eventCtx,
		eventCancel:  eventCancel,
	}

	// Attach monitors if provided
	if len(monitors) > 0 {
		sm.OnTransitioning(CreateMonitorCallback(name, monitors))
	}

	// Configure states in execution sequence order

	// Initializing - can only go to Starting or Error (per TLA+ ComponentTransition)
	sm.Configure("Initializing").
		Permit("Starting", "Starting").
		Permit("Error", "Error")

	// Starting - can go to Running, Error, or Stopping (per updated TLA+ spec)
	sm.Configure("Starting").
		Permit("Running", "Running").
		Permit("Error", "Error").
		Permit("Stopping", "Stopping").
		Permit("Stopped", "Stopped").
		OnEntry(csm.handleStarting)

	// Running - normal operation, can transition to many states
	sm.Configure("Running").
		Permit("Stopping", "Stopping").
		Permit("Stopped", "Stopped").
		Permit("Checkpointing", "Checkpointing").
		Permit("Restoring", "Restoring").
		Permit("Error", "Error").
		Permit("Crashed", "Crashed").
		Permit("Killed", "Killed")

	// Checkpointing - performing checkpoint operation
	sm.Configure("Checkpointing").
		Permit("Running", "Running").
		Permit("Error", "Error").
		OnEntry(csm.handleCheckpointing)

	// Restoring - performing restore operation
	sm.Configure("Restoring").
		Permit("Running", "Running").
		Permit("Error", "Error").
		OnEntry(csm.handleRestoring)

	// Stopping - graceful stop component
	sm.Configure("Stopping").
		Permit("Stopped", "Stopped").
		Permit("Error", "Error").
		Permit("Killed", "Killed").
		OnEntry(csm.handleStopping)

	// Stopped - terminal state, no transitions out

	// Terminal states - no transitions out
	sm.Configure("Error")
	sm.Configure("Crashed")
	sm.Configure("Killed")
	sm.Configure("Stopped")

	// Start listening for events from the component
	if component != nil {
		go csm.listenForEvents()
	}

	return csm
}

// listenForEvents reads from the component events channel and triggers state transitions
func (csm *ComponentState) listenForEvents() {
	events := csm.component.Events()
	for {
		select {
		case <-csm.eventCtx.Done():
			return
		case event := <-events:
			// Check if we're in a terminal state - if so, ignore all events
			currentState := csm.MustState().(string)
			if currentState == "Stopped" || currentState == "Error" || currentState == "Crashed" || currentState == "Killed" {
				// Component is in terminal state, ignore all events
				continue
			}

			switch event {
			case adapters.ComponentStarting:
				// Component reports it's starting - no state change needed, already in Starting
			case adapters.ComponentStarted:
				// Component successfully started - transition to Running
				// Wait for Ready to transition
			case adapters.ComponentStopping:
				// Component reports it's stopping - no state change needed, already in Stopping
			case adapters.ComponentStopped:
				// Component successfully stopped - transition to Stopped
				csm.FireAsync("Stopped")
			case adapters.ComponentChecking:
				// Component reports it's checking/ready - no specific state change
			case adapters.ComponentReady:
				// Component is ready - transition to Running if not already
				if currentState != "Running" {
					csm.FireAsync("Running")
				}
			case adapters.ComponentFailed:
				// Component failed - transition to Error
				csm.FireAsync("Error")
			default:
				// Unknown event, ignore
			}
		}
	}
}

// Close stops the event listener and cleans up resources
func (csm *ComponentState) Close() {
	// Check if component is already in a terminal state or stopping before calling Stop()
	currentState := csm.MustState().(string)
	isTerminalOrStopping := currentState == "Stopped" || currentState == "Error" || currentState == "Crashed" || currentState == "Killed" || currentState == "Stopping"

	// Close the underlying component (which will also stop it)
	if csm.component != nil && !isTerminalOrStopping {
		if closer, ok := csm.component.(interface{ Close() error }); ok {
			closer.Close()
		} else {
			// Fallback to Stop() if Close() is not available, but only if not already stopped
			csm.component.Stop()
		}
	}

	// Cancel the event listener context
	if csm.eventCancel != nil {
		csm.eventCancel()
	}
}

// handleStarting is called when entering Starting state - should start the component
func (csm *ComponentState) handleStarting(ctx context.Context, args ...any) error {
	if csm.component != nil {
		err := csm.component.Start(ctx)
		if err != nil {
			// Start failed - fire Error transition
			csm.FireAsync("Error")
			return nil
		}
	}
	return nil
}

// handleStopping is called when entering Stopping state - should stop the component
func (csm *ComponentState) handleStopping(ctx context.Context, args ...any) error {
	if csm.component != nil {
		csm.component.Stop()
	}
	return nil
}

// handleCheckpointing is called when entering Checkpointing state - should checkpoint the component
func (csm *ComponentState) handleCheckpointing(ctx context.Context, args ...any) error {
	if csm.component != nil {
		err := csm.component.Checkpoint()
		if err != nil {
			// Checkpoint failed - fire Error transition
			csm.FireAsync("Error")
			return nil
		}
	}
	return nil
}

// handleRestoring is called when entering Restoring state - should restore the component
func (csm *ComponentState) handleRestoring(ctx context.Context, args ...any) error {
	if csm.component != nil {
		err := csm.component.Restore()
		if err != nil {
			// Restore failed - fire Error transition
			csm.FireAsync("Error")
			return nil
		}
	}
	return nil
}

// Fire overrides the base Fire method
func (csm *ComponentState) Fire(trigger string, args ...any) error {
	err := csm.StateMachine.Fire(trigger, args...)
	return err
}

// FireAsync fires a trigger asynchronously to prevent deadlocks
func (csm *ComponentState) FireAsync(trigger string) {
	go func() {
		if err := csm.Fire(trigger); err != nil {
			// Check if we're in a terminal state - if so, ignore the error
			currentState := csm.MustState().(string)
			if currentState == "Stopped" || currentState == "Error" || currentState == "Crashed" || currentState == "Killed" {
				// Component is in terminal state, ignore invalid transitions
				return
			}
			panic(fmt.Sprintf("State machine error firing %s: %v", trigger, err))
		}
	}()
}
