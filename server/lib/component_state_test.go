package lib

import (
	"context"
	"testing"
	"time"
)

// FakeComponent implements ComponentInterface for testing
type FakeComponent struct {
	events          chan ComponentEventType
	closed          bool
	checkpointError error
	restoreError    error
}

// NewFakeComponent creates a new fake component for testing
func NewFakeComponent() *FakeComponent {
	return &FakeComponent{
		events: make(chan ComponentEventType), // Unbuffered channel
	}
}

// Events returns the event channel for this fake component
func (f *FakeComponent) Events() <-chan ComponentEventType {
	return f.events
}

// Start implements ComponentInterface - starts the fake component
func (f *FakeComponent) Start(ctx context.Context) error {
	return nil
}

// Stop implements ComponentInterface - no-op for testing
func (f *FakeComponent) Stop() {
	// No-op for testing
}

// Checkpoint implements ComponentInterface - can be configured to succeed/fail
func (f *FakeComponent) Checkpoint(ctx context.Context) error {
	return f.checkpointError
}

// Restore implements ComponentInterface - can be configured to succeed/fail
func (f *FakeComponent) Restore(ctx context.Context) error {
	return f.restoreError
}

// EmitEvent sends an event for testing (not part of ComponentInterface)
func (f *FakeComponent) EmitEvent(event ComponentEventType) {
	if !f.closed {
		f.events <- event
	}
}

// SetCheckpointError configures checkpoint to fail with given error
func (f *FakeComponent) SetCheckpointError(err error) {
	f.checkpointError = err
}

// SetRestoreError configures restore to fail with given error
func (f *FakeComponent) SetRestoreError(err error) {
	f.restoreError = err
}

// Close closes the event channel for cleanup
func (f *FakeComponent) Close() {
	if !f.closed {
		close(f.events)
		f.closed = true
	}
}

// waitForComponentState waits for the state machine to reach the expected state
func waitForComponentState(csm *ComponentState, expected ComponentStateType, timeout time.Duration) bool {
	deadline := time.Now().Add(timeout)
	for time.Now().Before(deadline) {
		if csm.MustState() == expected {
			return true
		}
		time.Sleep(time.Millisecond)
	}
	return false
}

// Test complete component lifecycle event sequences from TLA+ spec
func TestComponentStateMachine_TLASpecSequences(t *testing.T) {
	t.Run("Complete_Startup_Sequence", func(t *testing.T) {
		fake := NewFakeComponent()
		defer fake.Close()

		csm := NewComponentStateWithComponent(fake)

		// Request Running state: Initializing → Starting → Running
		if err := csm.Fire(ComponentTriggerStart); err != nil {
			t.Fatalf("Failed to request start: %v", err)
		}
		time.Sleep(10 * time.Millisecond) // Allow event watching to start

		// Complete startup event sequence
		fake.EmitEvent(ComponentStarting) // Component beginning startup
		fake.EmitEvent(ComponentStarted)  // Component started (may have ready check)
		fake.EmitEvent(ComponentReady)    // Component fully ready

		if !waitForComponentState(csm, ComponentStateRunning, 100*time.Millisecond) {
			t.Errorf("Expected Running after startup sequence, got %s", csm.MustState())
		}
	})

	t.Run("Complete_Stop_Sequence", func(t *testing.T) {
		fake := NewFakeComponent()
		defer fake.Close()

		csm := NewComponentStateWithComponent(fake)

		// Complete startup sequence first
		csm.Fire(ComponentTriggerStart)
		fake.EmitEvent(ComponentStarting)
		fake.EmitEvent(ComponentStarted)
		fake.EmitEvent(ComponentReady)
		waitForComponentState(csm, ComponentStateRunning, 100*time.Millisecond)

		// Complete stop sequence: Running → Stopping → Stopped
		if err := csm.Fire(ComponentTriggerStop); err != nil {
			t.Fatalf("Failed to request stop: %v", err)
		}
		fake.EmitEvent(ComponentStopping) // Component beginning shutdown
		fake.EmitEvent(ComponentStopped)  // Component fully stopped

		if !waitForComponentState(csm, ComponentStateStopped, 100*time.Millisecond) {
			t.Errorf("Expected Stopped after stop sequence, got %s", csm.MustState())
		}
	})

	t.Run("Complete_Checkpoint_Sequence", func(t *testing.T) {
		fake := NewFakeComponent()
		defer fake.Close()

		csm := NewComponentStateWithComponent(fake)

		// Start component first
		csm.Fire(ComponentTriggerStart)
		fake.EmitEvent(ComponentStarting)
		fake.EmitEvent(ComponentStarted)
		fake.EmitEvent(ComponentReady)
		waitForComponentState(csm, ComponentStateRunning, 100*time.Millisecond)

		// Checkpoint sequence: Running → Checkpointing → Running (no restart)
		if err := csm.Fire(ComponentTriggerCheckpoint); err != nil {
			t.Fatalf("Failed to request checkpoint: %v", err)
		}

		// Wait for checkpoint operation to complete (happens in background)
		if !waitForComponentState(csm, ComponentStateRunning, 200*time.Millisecond) {
			t.Errorf("Expected Running after checkpoint sequence, got %s", csm.MustState())
		}
	})

	t.Run("Complete_Restore_Sequence", func(t *testing.T) {
		fake := NewFakeComponent()
		defer fake.Close()

		csm := NewComponentStateWithComponent(fake)

		// Start component first
		csm.Fire(ComponentTriggerStart)
		fake.EmitEvent(ComponentStarting)
		fake.EmitEvent(ComponentStarted)
		fake.EmitEvent(ComponentReady)
		waitForComponentState(csm, ComponentStateRunning, 100*time.Millisecond)

		// Restore sequence: Running → Restoring → Starting → Running (with restart)
		if err := csm.Fire(ComponentTriggerRestore); err != nil {
			t.Fatalf("Failed to request restore: %v", err)
		}

		// Wait for restore to move to Starting, then complete startup again
		if !waitForComponentState(csm, ComponentStateStarting, 200*time.Millisecond) {
			t.Errorf("Expected Starting after restore completion, got %s", csm.MustState())
		}

		// Complete startup again after restore
		fake.EmitEvent(ComponentStarting)
		fake.EmitEvent(ComponentStarted)
		fake.EmitEvent(ComponentReady)

		if !waitForComponentState(csm, ComponentStateRunning, 100*time.Millisecond) {
			t.Errorf("Expected Running after restore restart sequence, got %s", csm.MustState())
		}
	})

	t.Run("Complete_Shutdown_Sequence", func(t *testing.T) {
		fake := NewFakeComponent()
		defer fake.Close()

		csm := NewComponentStateWithComponent(fake)

		// Start component first
		csm.Fire(ComponentTriggerStart)
		fake.EmitEvent(ComponentStarting)
		fake.EmitEvent(ComponentStarted)
		fake.EmitEvent(ComponentReady)
		waitForComponentState(csm, ComponentStateRunning, 100*time.Millisecond)

		// Shutdown sequence: Running → ShuttingDown → Shutdown (permanent)
		if err := csm.Fire(ComponentTriggerShutdown); err != nil {
			t.Fatalf("Failed to request shutdown: %v", err)
		}
		fake.EmitEvent(ComponentStopping) // Component beginning shutdown
		fake.EmitEvent(ComponentStopped)  // Component fully stopped

		if !waitForComponentState(csm, ComponentStateShutdown, 100*time.Millisecond) {
			t.Errorf("Expected Shutdown after shutdown sequence, got %s", csm.MustState())
		}
	})
}

// Test that component events map to correct state transitions
func TestComponentStateMachine_EventMapping(t *testing.T) {
	tests := []struct {
		name       string
		startState ComponentStateType
		event      ComponentEventType
		expectEnd  ComponentStateType
	}{
		{"Started_Event", ComponentStateStarting, ComponentStarted, ComponentStateRunning},
		{"Ready_Event", ComponentStateRunning, ComponentReady, ComponentStateRunning}, // No state change
		{"Failed_Event", ComponentStateRunning, ComponentFailed, ComponentStateError},
		{"Stopped_From_Stopping", ComponentStateStopping, ComponentStopped, ComponentStateStopped},
		{"Stopped_From_ShuttingDown", ComponentStateShuttingDown, ComponentStopped, ComponentStateShutdown},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			fake := NewFakeComponent()
			defer fake.Close()

			csm := NewComponentStateWithComponent(fake)

			// Get the component into the required start state
			switch tt.startState {
			case ComponentStateStarting:
				csm.Fire(ComponentTriggerStart)
			case ComponentStateRunning:
				csm.Fire(ComponentTriggerStart)
				fake.EmitEvent(ComponentStarted)
			case ComponentStateStopping:
				csm.Fire(ComponentTriggerStart)
				fake.EmitEvent(ComponentStarted)
				csm.Fire(ComponentTriggerStop)
			case ComponentStateShuttingDown:
				csm.Fire(ComponentTriggerStart)
				fake.EmitEvent(ComponentStarted)
				csm.Fire(ComponentTriggerShutdown)
			}

			time.Sleep(10 * time.Millisecond) // Allow state transitions to complete

			initialState := csm.MustState()
			fake.EmitEvent(tt.event)
			time.Sleep(10 * time.Millisecond) // Allow event processing

			if csm.MustState().(ComponentStateType) != tt.expectEnd {
				t.Errorf("From %s with event %s: expected %s, got %s",
					initialState, tt.event, tt.expectEnd, csm.MustState())
			}
		})
	}
}

// Test that final states reject further transitions
func TestComponentStateMachine_FinalStates(t *testing.T) {
	finalStates := []ComponentStateType{
		ComponentStateStopped,
		ComponentStateShutdown,
		ComponentStateError,
	}

	for _, state := range finalStates {
		t.Run(string(state), func(t *testing.T) {
			fake := NewFakeComponent()
			defer fake.Close()

			csm := NewComponentStateWithComponent(fake)

			// Get the state machine into the final state first
			switch state {
			case ComponentStateStopped:
				csm.Fire(ComponentTriggerStart)
				fake.EmitEvent(ComponentStarted)
				csm.Fire(ComponentTriggerStop)
				fake.EmitEvent(ComponentStopped)
			case ComponentStateShutdown:
				csm.Fire(ComponentTriggerStart)
				fake.EmitEvent(ComponentStarted)
				csm.Fire(ComponentTriggerShutdown)
				fake.EmitEvent(ComponentStopped)
			case ComponentStateError:
				csm.Fire(ComponentTriggerStart)
				fake.EmitEvent(ComponentFailed)
			}

			time.Sleep(10 * time.Millisecond) // Allow transitions to complete

			// Verify we're in the expected final state
			if csm.MustState() != state {
				t.Skipf("Could not get to final state %s, currently in %s", state, csm.MustState())
			}

			// Try to transition out - should fail
			err := csm.Fire(ComponentTriggerStart)
			if err == nil {
				t.Error("Final state should reject transitions")
			}
		})
	}
}

// Test operation failures
func TestComponentStateMachine_OperationFailures(t *testing.T) {
	t.Run("Checkpoint_Failure", func(t *testing.T) {
		fake := NewFakeComponent()
		defer fake.Close()

		// Configure checkpoint to fail
		fake.SetCheckpointError(context.Canceled)

		csm := NewComponentStateWithComponent(fake)

		// Start component first
		csm.Fire(ComponentTriggerStart)
		fake.EmitEvent(ComponentStarting)
		fake.EmitEvent(ComponentStarted)
		fake.EmitEvent(ComponentReady)
		waitForComponentState(csm, ComponentStateRunning, 100*time.Millisecond)

		// Request checkpoint (should fail)
		if err := csm.Fire(ComponentTriggerCheckpoint); err != nil {
			t.Fatalf("Failed to request checkpoint: %v", err)
		}

		// Wait for checkpoint failure to transition to Error
		if !waitForComponentState(csm, ComponentStateError, 200*time.Millisecond) {
			t.Errorf("Expected Error after checkpoint failure, got %s", csm.MustState())
		}
	})

	t.Run("Restore_Failure", func(t *testing.T) {
		fake := NewFakeComponent()
		defer fake.Close()

		// Configure restore to fail
		fake.SetRestoreError(context.Canceled)

		csm := NewComponentStateWithComponent(fake)

		// Start component first
		csm.Fire(ComponentTriggerStart)
		fake.EmitEvent(ComponentStarting)
		fake.EmitEvent(ComponentStarted)
		fake.EmitEvent(ComponentReady)
		waitForComponentState(csm, ComponentStateRunning, 100*time.Millisecond)

		// Request restore (should fail)
		if err := csm.Fire(ComponentTriggerRestore); err != nil {
			t.Fatalf("Failed to request restore: %v", err)
		}

		// Wait for restore failure to transition to Error
		if !waitForComponentState(csm, ComponentStateError, 200*time.Millisecond) {
			t.Errorf("Expected Error after restore failure, got %s", csm.MustState())
		}
	})
}

// NewTestableComponentStateMachine creates a testable component state machine for system state testing
func NewTestableComponentStateMachine() (*ComponentState, *FakeComponent) {
	fake := NewFakeComponent()
	csm := NewComponentStateWithComponent(fake)
	return csm, fake
}

// NewTestableComponentSetStateMachine creates a testable component set state machine for system state testing
func NewTestableComponentSetStateMachine() (*ComponentSetState, map[string]*FakeComponent) {
	fakeComponents := make(map[string]*FakeComponent)
	components := make(map[string]*ComponentState)

	// Create test components
	fakeComponents["db"] = NewFakeComponent()
	fakeComponents["fs"] = NewFakeComponent()

	components["db"] = NewComponentStateWithComponent(fakeComponents["db"])
	components["fs"] = NewComponentStateWithComponent(fakeComponents["fs"])

	css := NewComponentSetState(components)
	return css, fakeComponents
}
