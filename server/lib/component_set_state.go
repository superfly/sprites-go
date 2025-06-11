package lib

import (
	"context"
	"fmt"

	"github.com/qmuntal/stateless"
)

// ComponentSetStateType represents the overall state of a set of components
type ComponentSetStateType string

const (
	// Transition states
	ComponentSetStateInitializing  ComponentSetStateType = "Initializing"
	ComponentSetStateRestoring     ComponentSetStateType = "Restoring"
	ComponentSetStateCheckpointing ComponentSetStateType = "Checkpointing"
	ComponentSetStateShuttingDown  ComponentSetStateType = "ShuttingDown"

	// Final states
	ComponentSetStateShutdown ComponentSetStateType = "Shutdown"

	// Active states
	ComponentSetStateRunning ComponentSetStateType = "Running"

	// Error states
	ComponentSetStateError ComponentSetStateType = "Error"
)

// ComponentSetTrigger represents triggers for component set state changes
type ComponentSetTrigger string

const (
	ComponentSetTriggerStart              ComponentSetTrigger = "Start"
	ComponentSetTriggerShutdown           ComponentSetTrigger = "Shutdown"
	ComponentSetTriggerCheckpoint         ComponentSetTrigger = "Checkpoint"
	ComponentSetTriggerRestore            ComponentSetTrigger = "Restore"
	ComponentSetTriggerFailed             ComponentSetTrigger = "Failed"
	ComponentSetTriggerAllReady           ComponentSetTrigger = "AllReady"
	ComponentSetTriggerCheckpointComplete ComponentSetTrigger = "CheckpointComplete"
	ComponentSetTriggerRestoreComplete    ComponentSetTrigger = "RestoreComplete"
	ComponentSetTriggerShutdownComplete   ComponentSetTrigger = "ShutdownComplete"
)

// ComponentSetState manages the state of multiple named components
type ComponentSetState struct {
	*stateless.StateMachine
	components         map[string]*ComponentState
	shutdownInProgress bool
	stateChangeChan    chan struct{} // Unbuffered channel for state change notifications
}

// NewComponentSetState creates a new component set state machine with the given components
func NewComponentSetState(components map[string]*ComponentState) *ComponentSetState {
	// Make a copy to ensure immutability
	componentsCopy := make(map[string]*ComponentState)
	for name, component := range components {
		componentsCopy[name] = component
	}

	css := &ComponentSetState{
		components:      componentsCopy,
		stateChangeChan: make(chan struct{}), // Unbuffered channel
	}

	// Create the component set state machine with simple initial state
	css.StateMachine = stateless.NewStateMachine(ComponentSetStateInitializing)
	css.configureStateMachine()

	// Set up state transition tracking (removed event emission - was unused)

	// Activate the state machine to trigger OnEntry callbacks
	css.Activate()

	// Start the state evaluation processor
	go css.processStateChanges()

	// Register callbacks with each component to react to their state changes
	for name, component := range css.components {
		css.registerComponentCallback(name, component)
	}

	return css
}

// cleanup handles cleanup when entering final states
func (css *ComponentSetState) cleanup(ctx context.Context, args ...any) error {
	return nil
}

// startComponents starts all individual components (not used anymore, handled in Fire method)
func (css *ComponentSetState) startComponents(ctx context.Context, args ...any) error {
	for _, component := range css.components {
		component.Fire(ComponentTriggerStart)
	}
	return nil
}

// shutdownComponents initiates shutdown for all individual components
func (css *ComponentSetState) shutdownComponents(ctx context.Context, args ...any) error {
	for _, component := range css.components {
		component.Fire(ComponentTriggerShutdown)
	}
	return nil
}

// checkpointComponents initiates checkpoint for all individual components
func (css *ComponentSetState) checkpointComponents(ctx context.Context, args ...any) error {
	for _, component := range css.components {
		component.Fire(ComponentTriggerCheckpoint)
	}
	return nil
}

// restoreComponents initiates restore for all individual components
func (css *ComponentSetState) restoreComponents(ctx context.Context, args ...any) error {
	for _, component := range css.components {
		component.Fire(ComponentTriggerRestore)
	}
	return nil
}

// configureStateMachine sets up the component set state machine transitions
func (css *ComponentSetState) configureStateMachine() {
	// From Initializing
	css.Configure(ComponentSetStateInitializing).
		Ignore(ComponentSetTriggerStart).
		Permit(ComponentSetTriggerAllReady, ComponentSetStateRunning).
		Permit(ComponentSetTriggerShutdown, ComponentSetStateShuttingDown).
		Permit(ComponentSetTriggerFailed, ComponentSetStateError)

	// From Running
	css.Configure(ComponentSetStateRunning).
		Ignore(ComponentSetTriggerStart).
		Permit(ComponentSetTriggerCheckpoint, ComponentSetStateCheckpointing).
		Permit(ComponentSetTriggerRestore, ComponentSetStateRestoring).
		Permit(ComponentSetTriggerShutdown, ComponentSetStateShuttingDown).
		Permit(ComponentSetTriggerFailed, ComponentSetStateError)

	// From Checkpointing
	css.Configure(ComponentSetStateCheckpointing).
		Permit(ComponentSetTriggerCheckpointComplete, ComponentSetStateRunning).
		Permit(ComponentSetTriggerFailed, ComponentSetStateError)

	// From Restoring
	css.Configure(ComponentSetStateRestoring).
		Permit(ComponentSetTriggerRestoreComplete, ComponentSetStateRunning).
		Permit(ComponentSetTriggerFailed, ComponentSetStateError)

	// From ShuttingDown
	css.Configure(ComponentSetStateShuttingDown).
		OnEntry(css.shutdownComponents).
		Permit(ComponentSetTriggerShutdownComplete, ComponentSetStateShutdown).
		Permit(ComponentSetTriggerFailed, ComponentSetStateError)

	// State-specific OnEntry handlers
	css.Configure(ComponentSetStateCheckpointing).OnEntry(css.checkpointComponents)
	css.Configure(ComponentSetStateRestoring).OnEntry(css.restoreComponents)

	// Final states - explicitly configure even though they have no outgoing transitions
	css.Configure(ComponentSetStateShutdown).OnEntry(css.cleanup)
	css.Configure(ComponentSetStateError).OnEntry(css.cleanup)
}

// registerComponentCallback registers an OnTransitioned callback with a component
func (css *ComponentSetState) registerComponentCallback(name string, component *ComponentState) {
	component.OnTransitioned(func(ctx context.Context, transition stateless.Transition) {
		newComponentState := ComponentStateType(transition.Destination.(ComponentStateType))
		css.handleComponentStateChange(name, newComponentState)
	})
}

// processStateChanges runs in a goroutine to handle state change notifications
func (css *ComponentSetState) processStateChanges() {
	for range css.stateChangeChan {
		css.evaluateStateTransition()
	}
}

// handleComponentStateChange processes a component state change and makes transitions if needed
func (css *ComponentSetState) handleComponentStateChange(componentName string, newState ComponentStateType) {
	// Only trigger evaluation for states that could affect ComponentSet transitions
	switch newState {
	case ComponentStateRunning, ComponentStateError, ComponentStateShutdown:
		// Send notification on unbuffered channel (blocks until processed)
		css.stateChangeChan <- struct{}{}
	}
	// Other states (Starting, Stopping, etc.) don't trigger ComponentSet evaluation
}

// evaluateStateTransition checks if ComponentSetStateMachine should transition based on component states
func (css *ComponentSetState) evaluateStateTransition() {
	currentState := ComponentSetStateType(css.MustState().(ComponentSetStateType))

	// Count component states
	runningCount := 0
	shutdownCount := 0
	errorCount := 0

	for _, component := range css.components {
		state := ComponentStateType(component.MustState().(ComponentStateType))
		switch state {
		case ComponentStateRunning:
			runningCount++
		case ComponentStateShutdown:
			shutdownCount++
		case ComponentStateError:
			errorCount++
		}
	}

	totalComponents := len(css.components)

	// Handle error states first
	if errorCount > 0 && currentState != ComponentSetStateError {
		css.Fire(ComponentSetTriggerFailed)
		return
	}

	// Handle automatic transitions based on counts (matching TLA+ spec)
	if runningCount == totalComponents {
		if currentState == ComponentSetStateInitializing {
			// Automatic transition: Initializing -> Running when all components ready
			css.Fire(ComponentSetTriggerAllReady)
		} else if currentState == ComponentSetStateCheckpointing {
			// Automatic transition: Checkpointing -> Running when all components ready
			css.Fire(ComponentSetTriggerCheckpointComplete)
		} else if currentState == ComponentSetStateRestoring {
			// Automatic transition: Restoring -> Running when all components ready
			css.Fire(ComponentSetTriggerRestoreComplete)
		}
	} else if shutdownCount == totalComponents && currentState == ComponentSetStateShuttingDown {
		// Automatic transition: ShuttingDown -> Shutdown when all components shutdown
		css.Fire(ComponentSetTriggerShutdownComplete)
	}
}

// GetComponentState returns the current state of a named component
func (css *ComponentSetState) GetComponentState(name string) (ComponentStateType, error) {
	component, exists := css.components[name]
	if !exists {
		return "", fmt.Errorf("component %s not found", name)
	}
	return ComponentStateType(component.MustState().(ComponentStateType)), nil
}

// GetComponentStates returns the current states of all components
func (css *ComponentSetState) GetComponentStates() map[string]ComponentStateType {
	states := make(map[string]ComponentStateType)
	for name, component := range css.components {
		states[name] = ComponentStateType(component.MustState().(ComponentStateType))
	}
	return states
}

// ListComponents returns the names of all managed components
func (css *ComponentSetState) ListComponents() []string {
	names := make([]string, 0, len(css.components))
	for name := range css.components {
		names = append(names, name)
	}
	return names
}

// AddStateChangeCallback adds a callback that will be called on component set state changes
func (css *ComponentSetState) AddStateChangeCallback(callback func(stateless.Transition)) {
	css.OnTransitioned(func(ctx context.Context, transition stateless.Transition) {
		callback(transition)
	})
}

// AddComponentStateChangeCallback adds a callback that will be called on any individual component state change
func (css *ComponentSetState) AddComponentStateChangeCallback(callback func()) {
	for _, component := range css.components {
		component.OnTransitioned(func(ctx context.Context, transition stateless.Transition) {
			callback()
		})
	}
}

// AddComponentTransitionCallback adds a callback that will be called on any individual component state change
// with the component name and transition information
func (css *ComponentSetState) AddComponentTransitionCallback(callback func(componentName string, transition stateless.Transition)) {
	for name, component := range css.components {
		componentName := name // Capture the name for the closure
		component.OnTransitioned(func(ctx context.Context, transition stateless.Transition) {
			callback(componentName+"Component", transition)
		})
	}
}

func (css *ComponentSetState) GetState() ComponentSetStateType {
	return ComponentSetStateType(css.MustState().(ComponentSetStateType))
}

// Fire wraps the stateless.StateMachine.Fire method to handle Start trigger specially
func (css *ComponentSetState) Fire(trigger ComponentSetTrigger, args ...any) error {
	// Handle Start trigger specially - start components if in Initializing state
	if trigger == ComponentSetTriggerStart && css.MustState() == ComponentSetStateInitializing {
		for _, component := range css.components {
			component.Fire(ComponentTriggerStart)
		}
	}

	return css.StateMachine.Fire(trigger, args...)
}
