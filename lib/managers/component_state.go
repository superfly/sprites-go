package managers

import (
	"context"
	"fmt"

	"github.com/qmuntal/stateless"
)

// ManagedComponent defines the interface for a component that can be managed by ComponentState
type ManagedComponent interface {
	GetName() string
	Start(ctx context.Context) error
	Ready() error
	Checkpoint(id string) error
	Restore(id string) error
	Stop()
}

// ComponentState is a purely declarative intent processor for component states
// Following cursor rules: extends stateless.StateMachine
type ComponentState struct {
	*stateless.StateMachine
	name      string
	component ManagedComponent
}

// Fire overrides the base Fire method
func (csm *ComponentState) Fire(trigger string, args ...any) error {
	err := csm.StateMachine.Fire(trigger, args...)
	return err
}

// NewComponentState creates a new component state manager
// Initial state is "Initializing" as per spec: Init == components = [i \in 1..N |-> "Initializing"]
func NewComponentState(name string, component ManagedComponent) *ComponentState {
	sm := stateless.NewStateMachine("Initializing")

	csm := &ComponentState{
		StateMachine: sm,
		name:         name,
		component:    component,
	}

	// Configure states based on ComponentTransition definition

	// Initializing - can only go to Starting or Error
	sm.Configure("Initializing").
		Permit("Starting", "Starting").
		Permit("Error", "Error")

	// Starting - can go to Running, Error, or Stopping
	sm.Configure("Starting").
		Permit("Running", "Running").
		Permit("Error", "Error").
		Permit("Stopping", "Stopping"). // Allow stopping during startup for error recovery
		OnEntry(csm.handleStarting)

	// Running - normal operation, can checkpoint/restore or stop
	sm.Configure("Running").
		Permit("Stopping", "Stopping").
		Permit("Error", "Error").
		Permit("Checkpointing", "Checkpointing").
		Permit("Restoring", "Restoring")

	// Checkpointing - performing checkpoint operation
	sm.Configure("Checkpointing").
		Permit("Running", "Running"). // Success - back to Running
		Permit("Error", "Error").     // Failure - to Error
		OnEntry(csm.handleCheckpointing)

	// Restoring - performing restore operation
	sm.Configure("Restoring").
		Permit("Running", "Running"). // Success - back to Running
		Permit("Error", "Error").     // Failure - to Error
		OnEntry(csm.handleRestoring)

	// Stopping - shutting down component gracefully
	sm.Configure("Stopping").
		Permit("Stopped", "Stopped").
		Permit("Error", "Error").
		OnEntry(csm.handleStopping)

	// Terminal states - no transitions out
	sm.Configure("Stopped")
	sm.Configure("Error")

	return csm
}

// handleStarting is called when entering Starting state - should start the component
func (csm *ComponentState) handleStarting(ctx context.Context, args ...any) error {
	if csm.component != nil {
		// Start the component
		if err := csm.component.Start(ctx); err != nil {
			// Start failed - fire Error transition
			if fireErr := csm.Fire("Error"); fireErr != nil {
				panic(fmt.Sprintf("State machine error firing Error: %v", fireErr))
			}
			return nil
		}

		// Check if ready
		if err := csm.component.Ready(); err == nil {
			// Component is ready - transition to Running
			if fireErr := csm.Fire("Running"); fireErr != nil {
				panic(fmt.Sprintf("State machine error firing Running: %v", fireErr))
			}
		} else {
			// Not ready yet or ready failed - stay in Starting or transition to Error
			// For now, let's assume the component will handle retries internally
		}
	}
	return nil
}

// handleCheckpointing is called when entering Checkpointing state
func (csm *ComponentState) handleCheckpointing(ctx context.Context, args ...any) error {
	// Extract checkpoint ID from args if provided
	checkpointID := ""
	if len(args) > 0 {
		if id, ok := args[0].(string); ok {
			checkpointID = id
		}
	}

	if csm.component != nil {
		// Perform checkpoint
		if err := csm.component.Checkpoint(checkpointID); err != nil {
			// Checkpoint failed - transition to Error
			if fireErr := csm.Fire("Error"); fireErr != nil {
				panic(fmt.Sprintf("State machine error firing Error: %v", fireErr))
			}
			return nil
		}

		// Checkpoint succeeded - transition back to Running
		if fireErr := csm.Fire("Running"); fireErr != nil {
			panic(fmt.Sprintf("State machine error firing Running: %v", fireErr))
		}
	}
	return nil
}

// handleRestoring is called when entering Restoring state
func (csm *ComponentState) handleRestoring(ctx context.Context, args ...any) error {
	// Extract checkpoint ID from args if provided
	checkpointID := ""
	if len(args) > 0 {
		if id, ok := args[0].(string); ok {
			checkpointID = id
		}
	}

	if csm.component != nil {
		// Perform restore
		if err := csm.component.Restore(checkpointID); err != nil {
			// Restore failed - transition to Error
			if fireErr := csm.Fire("Error"); fireErr != nil {
				panic(fmt.Sprintf("State machine error firing Error: %v", fireErr))
			}
			return nil
		}

		// Restore succeeded - transition back to Running
		if fireErr := csm.Fire("Running"); fireErr != nil {
			panic(fmt.Sprintf("State machine error firing Running: %v", fireErr))
		}
	}
	return nil
}

// handleStopping is called when entering Stopping state - should stop the component
func (csm *ComponentState) handleStopping(ctx context.Context, args ...any) error {
	if csm.component != nil {
		// Stop the component
		csm.component.Stop()

		// Component stopped successfully - transition to Stopped
		if fireErr := csm.Fire("Stopped"); fireErr != nil {
			panic(fmt.Sprintf("State machine error firing Stopped: %v", fireErr))
		}
	}
	return nil
}

// GetComponent returns the underlying managed component
func (csm *ComponentState) GetComponent() ManagedComponent {
	return csm.component
}

// Close stops any background goroutines (none in this case)
func (csm *ComponentState) Close() {
	// No cleanup needed
}
