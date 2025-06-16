package managers

import (
	"context"
	"fmt"

	"github.com/qmuntal/stateless"
)

// ComponentGroupConfig holds the configuration for a component group state manager
type ComponentGroupConfig struct {
	InitialState      string // Initial state, defaults to "Initializing"
	Components        []ManagedComponent
	ComponentMonitors []StateMonitor // Separate field for monitors to pass to individual components
}

// ComponentTransition represents a component state transition
type ComponentTransition struct {
	Source      string
	Destination string
}

// componentGroupMonitor implements StateMonitor to track individual component state changes
type componentGroupMonitor struct {
	events       chan StateTransition
	cgsm         *ComponentGroupState
	componentIdx int
	healthyCount int
	errorCount   int
	stoppedCount int
}

// Events implements StateMonitor interface
func (cgm *componentGroupMonitor) Events() chan<- StateTransition {
	return cgm.events
}

// processEvents processes events from all components using shared state tracking
func (cgm *componentGroupMonitor) processEvents() {
	totalComponents := len(cgm.cgsm.config.Components)

	for transition := range cgm.events {
		// Update shared counts based on source state (decrement)
		if transition.From == "Running" {
			cgm.healthyCount--
		} else if transition.From == "Error" {
			cgm.errorCount--
		} else if transition.From == "Stopped" {
			cgm.stoppedCount--
		}

		// Update shared counts based on destination state (increment)
		if transition.To == "Running" {
			cgm.healthyCount++
		} else if transition.To == "Error" {
			cgm.errorCount++
		} else if transition.To == "Stopped" {
			cgm.stoppedCount++
		}

		// Check if we should transition to Running (only once when all components are healthy)
		currentState := cgm.cgsm.MustState().(string)
		if cgm.healthyCount == totalComponents && currentState == "Starting" {
			if err := cgm.cgsm.Fire("Running"); err != nil {
				panic(fmt.Sprintf("State machine error firing Running: %v", err))
			}
		}

		// Check current state and decide transitions (reuse currentState variable)

		// If any component is in error, transition to ErrorStopping (if not already there)
		if cgm.errorCount > 0 && currentState != "ErrorStopping" && currentState != "Error" {
			if err := cgm.cgsm.Fire("ErrorStopping"); err != nil {
				panic(fmt.Sprintf("State machine error firing ErrorStopping: %v", err))
			}
		} else if currentState == "ErrorStopping" && (cgm.errorCount+cgm.stoppedCount) == totalComponents {
			// In ErrorStopping and all components are either Error or Stopped (no healthy components left)
			// Transition to final Error state
			if err := cgm.cgsm.Fire("Error"); err != nil {
				panic(fmt.Sprintf("State machine error firing Error: %v", err))
			}
		} else if cgm.stoppedCount == totalComponents && currentState == "Stopping" {
			// All components are stopped, transition to Stopped
			if err := cgm.cgsm.Fire("Stopped"); err != nil {
				panic(fmt.Sprintf("State machine error firing Stopped: %v", err))
			}
		}
	}
}

// ComponentGroupState is a purely declarative intent processor for component group states
// Following cursor rules: extends stateless.StateMachine
type ComponentGroupState struct {
	*stateless.StateMachine
	config            ComponentGroupConfig
	componentManagers []*ComponentState
	sharedMonitor     *componentGroupMonitor
	monitorCtx        context.Context
	monitorCancel     context.CancelFunc
}

// Fire overrides the base Fire method
func (cgsm *ComponentGroupState) Fire(trigger string, args ...any) error {
	err := cgsm.StateMachine.Fire(trigger, args...)
	return err
}

// NewComponentGroupState creates a new component group state manager
// Initial state is "Initializing" as per TLA+ spec (unless overridden in config)
// monitors parameter uses splat - these are for the ComponentGroupState itself
// config.ComponentMonitors are passed to individual components
func NewComponentGroupState(config ComponentGroupConfig, monitors ...StateMonitor) *ComponentGroupState {
	initialState := config.InitialState
	if initialState == "" {
		initialState = "Initializing" // Default per TLA+ spec
	}
	sm := stateless.NewStateMachine(initialState)

	monitorCtx, monitorCancel := context.WithCancel(context.Background())

	cgsm := &ComponentGroupState{
		StateMachine:      sm,
		config:            config,
		componentManagers: make([]*ComponentState, 0, len(config.Components)),
		monitorCtx:        monitorCtx,
		monitorCancel:     monitorCancel,
	}

	// Create shared monitor that will track all component state changes
	sharedMonitor := &componentGroupMonitor{
		events:       make(chan StateTransition, 100),
		cgsm:         cgsm,
		componentIdx: -1, // -1 indicates this is the shared monitor
		healthyCount: 0,
		errorCount:   0,
		stoppedCount: 0,
	}
	cgsm.sharedMonitor = sharedMonitor

	// Start processing events for the shared monitor
	go sharedMonitor.processEvents()

	// Attach monitors to the ComponentGroupState itself (using splat monitors)
	if len(monitors) > 0 {
		sm.OnTransitioning(CreateMonitorCallback("ComponentGroupStateManager", monitors))
	}

	// Create ComponentStateManager instances for each component
	for _, component := range config.Components {
		// Pass the shared monitor for internal coordination AND the component-specific monitors
		// Use the separate ComponentMonitors field for what we send to individual components
		componentMonitors := append([]StateMonitor{sharedMonitor}, config.ComponentMonitors...)

		componentName := component.GetName() + "Component"
		componentManager := NewComponentState(componentName, component, componentMonitors)
		cgsm.componentManagers = append(cgsm.componentManagers, componentManager)
	}

	// Configure component group states based on TLA+ ComponentSet definition

	// Initializing - components starting up
	sm.Configure("Initializing").
		Permit("Starting", "Starting")

	// Starting - components transitioning to active
	sm.Configure("Starting").
		Permit("Running", "Running").
		Permit("Stopping", "Stopping").
		Permit("ErrorStopping", "ErrorStopping").
		OnEntry(cgsm.handleStarting)

	// Running - all components operational
	sm.Configure("Running").
		Permit("Stopping", "Stopping").
		Permit("ErrorStopping", "ErrorStopping").
		Permit("Error", "Error")

	// ErrorStopping - component failed, system needs to know
	sm.Configure("ErrorStopping").
		Ignore("ErrorStopping").
		Permit("Stopping", "Stopping").
		Permit("Error", "Error").
		OnEntry(cgsm.handleErrorStopping)

	// Stopping - components stopping gracefully
	sm.Configure("Stopping").
		Permit("Stopped", "Stopped").
		Permit("Error", "Error").
		OnEntry(cgsm.handleStopping)

	// Terminal states - no transitions out
	sm.Configure("Error")   // Terminal error state
	sm.Configure("Stopped") // Terminal stopped state

	return cgsm
}

// handleStarting is called when entering Starting state - should start all components
func (cgsm *ComponentGroupState) handleStarting(ctx context.Context, args ...any) error {
	for _, componentManager := range cgsm.componentManagers {
		// Fire on components - synchronous because this is parent->child
		componentManager.Fire("Starting")
	}
	return nil
}

// handleErrorStopping is called when entering ErrorStopping state - stops healthy components during error recovery
func (cgsm *ComponentGroupState) handleErrorStopping(ctx context.Context, args ...any) error {
	for _, componentManager := range cgsm.componentManagers {
		currentState := componentManager.MustState().(string)
		// Stop all non-failed components - let the component handle when it can actually stop
		if currentState != "Error" && currentState != "Stopped" && currentState != "Stopping" {
			// Call Stop() on the underlying component - it will handle timing and fire events
			if componentManager.component != nil {
				componentManager.component.Stop()
			}
		}
	}
	return nil
}

// handleStopping is called when entering Stopping state - stops remaining healthy components
func (cgsm *ComponentGroupState) handleStopping(ctx context.Context, args ...any) error {
	for _, componentManager := range cgsm.componentManagers {
		// Fire on components - synchronous because this is parent->child
		componentManager.Fire("Stopping")
	}
	return nil
}

// GetComponentStates returns the individual component state managers for testing
func (cgsm *ComponentGroupState) GetComponentStates() []*ComponentState {
	return cgsm.componentManagers
}

// Close stops the component monitoring and cleans up resources
func (cgsm *ComponentGroupState) Close() {
	// Close all component managers first
	for _, componentManager := range cgsm.componentManagers {
		componentManager.Close()
	}

	if cgsm.monitorCancel != nil {
		cgsm.monitorCancel()
		cgsm.monitorCancel = nil // Prevent double-cancel
	}

	// Close the shared monitor channel (check if already closed)
	if cgsm.sharedMonitor != nil && cgsm.sharedMonitor.events != nil {
		close(cgsm.sharedMonitor.events)
		cgsm.sharedMonitor.events = nil // Prevent double-close
	}
}
