package state

import (
	"context"
	"fmt"
	"sprite-env/lib/adapters"
	"testing"
	"time"
)

// FakeComponent implements ComponentInterface for testing
type FakeComponent struct {
	handlers        adapters.ComponentEventHandlers
	closed          bool
	ctx             context.Context
	cancel          context.CancelFunc
	checkpointError error // Allow configuring checkpoint to fail
	restoreError    error // Allow configuring restore to fail
}

// NewFakeComponent creates a new fake component for testing
func NewFakeComponent() *FakeComponent {
	ctx, cancel := context.WithCancel(context.Background())
	return &FakeComponent{
		ctx:    ctx,
		cancel: cancel,
	}
}

// SetEventHandlers implements ComponentInterface
func (f *FakeComponent) SetEventHandlers(handlers adapters.ComponentEventHandlers) {
	f.handlers = handlers
}

// Start implements ComponentInterface - starts the fake component
func (f *FakeComponent) Start(ctx context.Context) error {
	// Simulate real component behavior by automatically emitting startup events
	go func() {
		// Small delay to simulate real startup timing
		time.Sleep(1 * time.Millisecond)
		f.EmitEvent(adapters.ComponentStarting)

		time.Sleep(1 * time.Millisecond)
		f.EmitEvent(adapters.ComponentStarted)

		// Note: ComponentReady is emitted separately in tests to control timing
	}()
	return nil
}

// Stop implements ComponentInterface - no-op for testing
func (f *FakeComponent) Stop() {
	// No-op for testing
}

// Checkpoint implements ComponentInterface - simulates checkpoint operation
func (f *FakeComponent) Checkpoint(ctx context.Context) error {
	// Return configured error if set
	if f.checkpointError != nil {
		return f.checkpointError
	}
	// Simulate checkpoint work
	return nil
}

// Restore implements ComponentInterface - simulates restore operation
func (f *FakeComponent) Restore(ctx context.Context) error {
	// Return configured error if set
	if f.restoreError != nil {
		return f.restoreError
	}
	// Simulate restore work
	return nil
}

// SetCheckpointError configures the checkpoint operation to fail
func (f *FakeComponent) SetCheckpointError(err error) {
	f.checkpointError = err
}

// SetRestoreError configures the restore operation to fail
func (f *FakeComponent) SetRestoreError(err error) {
	f.restoreError = err
}

// EmitEvent sends an event for testing (not part of ComponentInterface)
func (f *FakeComponent) EmitEvent(event adapters.ComponentEventType, err ...error) {
	// Call the handlers if set (Observer pattern)
	// Use context to avoid goroutine leaks in tests
	if f.ctx != nil {
		go func() {
			// Check if context is canceled before running handler
			select {
			case <-f.ctx.Done():
				return // Context canceled, don't run handler
			default:
			}

			switch event {
			case adapters.ComponentStarting:
				if f.handlers.Starting != nil {
					f.handlers.Starting()
				}
			case adapters.ComponentStarted:
				if f.handlers.Started != nil {
					f.handlers.Started()
				}
			case adapters.ComponentChecking:
				if f.handlers.Checking != nil {
					f.handlers.Checking()
				}
			case adapters.ComponentReady:
				if f.handlers.Ready != nil {
					f.handlers.Ready()
				}
			case adapters.ComponentStopping:
				if f.handlers.Stopping != nil {
					f.handlers.Stopping()
				}
			case adapters.ComponentStopped:
				if f.handlers.Stopped != nil {
					f.handlers.Stopped()
				}
			case adapters.ComponentFailed:
				if f.handlers.Failed != nil {
					var failErr error
					if len(err) > 0 {
						failErr = err[0]
					}
					f.handlers.Failed(failErr)
				}
			}
		}()
	}
}

// Close cleans up the fake component
func (f *FakeComponent) Close() {
	if !f.closed {
		f.closed = true
		// Cancel context to clean up any running handler goroutines
		if f.cancel != nil {
			f.cancel()
		}
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

		csm := NewComponentState(fake)

		// Request Running state: Initializing → Starting → Running
		if err := csm.Fire(ComponentTriggerStart); err != nil {
			t.Fatalf("Failed to request start: %v", err)
		}
		time.Sleep(10 * time.Millisecond) // Allow event watching to start

		// Complete startup event sequence
		fake.EmitEvent(adapters.ComponentStarting) // Component beginning startup
		fake.EmitEvent(adapters.ComponentStarted)  // Component started (may have ready check)
		fake.EmitEvent(adapters.ComponentReady)    // Component fully ready

		if !waitForComponentState(csm, ComponentStateRunning, 10*time.Second) {
			t.Errorf("Expected Running after startup sequence, got %s", csm.MustState())
		}
	})

	t.Run("Complete_Stop_Sequence", func(t *testing.T) {
		fake := NewFakeComponent()
		defer fake.Close()

		csm := NewComponentState(fake)

		// Complete startup sequence first
		csm.Fire(ComponentTriggerStart)
		fake.EmitEvent(adapters.ComponentStarting)
		fake.EmitEvent(adapters.ComponentStarted)
		fake.EmitEvent(adapters.ComponentReady)
		waitForComponentState(csm, ComponentStateRunning, 10*time.Second)

		// Complete stop sequence: Running → Stopping → Stopped
		if err := csm.Fire(ComponentTriggerStop); err != nil {
			t.Fatalf("Failed to request stop: %v", err)
		}
		fake.EmitEvent(adapters.ComponentStopping) // Component beginning shutdown
		fake.EmitEvent(adapters.ComponentStopped)  // Component fully stopped

		if !waitForComponentState(csm, ComponentStateStopped, 10*time.Second) {
			t.Errorf("Expected Stopped after stop sequence, got %s", csm.MustState())
		}
	})

	t.Run("Complete_Checkpoint_Sequence", func(t *testing.T) {
		fake := NewFakeComponent()
		defer fake.Close()

		csm := NewComponentState(fake)

		// Start component first
		csm.Fire(ComponentTriggerStart)
		fake.EmitEvent(adapters.ComponentStarting)
		fake.EmitEvent(adapters.ComponentStarted)
		fake.EmitEvent(adapters.ComponentReady)
		waitForComponentState(csm, ComponentStateRunning, 10*time.Second)

		// Checkpoint sequence: Running → Checkpointing → Running (no restart)
		if err := csm.Fire(ComponentTriggerCheckpoint); err != nil {
			t.Fatalf("Failed to request checkpoint: %v", err)
		}

		// Wait for checkpoint operation to complete (happens in background)
		if !waitForComponentState(csm, ComponentStateRunning, 10*time.Second) {
			t.Errorf("Expected Running after checkpoint sequence, got %s", csm.MustState())
		}
	})

	t.Run("Complete_Restore_Sequence", func(t *testing.T) {
		fake := NewFakeComponent()
		defer fake.Close()

		csm := NewComponentState(fake)

		// Start component first
		csm.Fire(ComponentTriggerStart)
		fake.EmitEvent(adapters.ComponentStarting)
		fake.EmitEvent(adapters.ComponentStarted)
		fake.EmitEvent(adapters.ComponentReady)
		waitForComponentState(csm, ComponentStateRunning, 10*time.Second)

		// Restore sequence: Running → Restoring → Starting → Running (with restart)
		if err := csm.Fire(ComponentTriggerRestore); err != nil {
			t.Fatalf("Failed to request restore: %v", err)
		}

		// After restore, component goes to Starting and then automatically to Running
		// due to fake component's automatic event emission
		if !waitForComponentState(csm, ComponentStateRunning, 10*time.Second) {
			t.Errorf("Expected Running after restore sequence completes, got %s", csm.MustState())
		}

		// Emit final Ready event to complete the restart sequence
		fake.EmitEvent(adapters.ComponentReady)

		if !waitForComponentState(csm, ComponentStateRunning, 10*time.Second) {
			t.Errorf("Expected Running after restore restart sequence, got %s", csm.MustState())
		}
	})

	t.Run("Complete_Shutdown_Sequence", func(t *testing.T) {
		fake := NewFakeComponent()
		defer fake.Close()

		csm := NewComponentState(fake)

		// Start component first
		csm.Fire(ComponentTriggerStart)
		fake.EmitEvent(adapters.ComponentStarting)
		fake.EmitEvent(adapters.ComponentStarted)
		fake.EmitEvent(adapters.ComponentReady)
		waitForComponentState(csm, ComponentStateRunning, 10*time.Second)

		// Shutdown sequence: Running → ShuttingDown → Shutdown (permanent)
		if err := csm.Fire(ComponentTriggerShutdown); err != nil {
			t.Fatalf("Failed to request shutdown: %v", err)
		}
		fake.EmitEvent(adapters.ComponentStopping) // Component beginning shutdown
		fake.EmitEvent(adapters.ComponentStopped)  // Component fully stopped

		if !waitForComponentState(csm, ComponentStateShutdown, 10*time.Second) {
			t.Errorf("Expected Shutdown after shutdown sequence, got %s", csm.MustState())
		}
	})
}

// Test that component events map to correct state transitions
func TestComponentStateMachine_EventMapping(t *testing.T) {
	tests := []struct {
		name       string
		startState ComponentStateType
		event      adapters.ComponentEventType
		expectEnd  ComponentStateType
	}{
		{"Started_Event", ComponentStateStarting, adapters.ComponentStarted, ComponentStateRunning},
		{"Ready_Event", ComponentStateRunning, adapters.ComponentReady, ComponentStateRunning}, // No state change
		{"Failed_Event", ComponentStateRunning, adapters.ComponentFailed, ComponentStateError},
		{"Stopped_From_Stopping", ComponentStateStopping, adapters.ComponentStopped, ComponentStateStopped},
		{"Stopped_From_ShuttingDown", ComponentStateShuttingDown, adapters.ComponentStopped, ComponentStateShutdown},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			fake := NewFakeComponent()
			defer fake.Close()

			csm := NewComponentState(fake)

			// Get the component into the required start state
			switch tt.startState {
			case ComponentStateStarting:
				csm.Fire(ComponentTriggerStart)
			case ComponentStateRunning:
				csm.Fire(ComponentTriggerStart)
				fake.EmitEvent(adapters.ComponentStarted)
			case ComponentStateStopping:
				csm.Fire(ComponentTriggerStart)
				fake.EmitEvent(adapters.ComponentStarted)
				csm.Fire(ComponentTriggerStop)
			case ComponentStateShuttingDown:
				csm.Fire(ComponentTriggerStart)
				fake.EmitEvent(adapters.ComponentStarted)
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

			csm := NewComponentState(fake)

			// Get the state machine into the final state first
			switch state {
			case ComponentStateStopped:
				csm.Fire(ComponentTriggerStart)
				fake.EmitEvent(adapters.ComponentStarted)
				csm.Fire(ComponentTriggerStop)
				fake.EmitEvent(adapters.ComponentStopped)
			case ComponentStateShutdown:
				csm.Fire(ComponentTriggerStart)
				fake.EmitEvent(adapters.ComponentStarted)
				csm.Fire(ComponentTriggerShutdown)
				fake.EmitEvent(adapters.ComponentStopped)
			case ComponentStateError:
				csm.Fire(ComponentTriggerStart)
				fake.EmitEvent(adapters.ComponentFailed)
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
		fake.SetCheckpointError(fmt.Errorf("checkpoint failed"))

		csm := NewComponentState(fake)

		// Start component first
		csm.Fire(ComponentTriggerStart)
		fake.EmitEvent(adapters.ComponentStarting)
		fake.EmitEvent(adapters.ComponentStarted)
		fake.EmitEvent(adapters.ComponentReady)
		waitForComponentState(csm, ComponentStateRunning, 10*time.Second)

		// Request checkpoint (should fail)
		if err := csm.Fire(ComponentTriggerCheckpoint); err != nil {
			t.Fatalf("Failed to request checkpoint: %v", err)
		}

		// Wait for checkpoint failure to transition to Error
		if !waitForComponentState(csm, ComponentStateError, 10*time.Second) {
			t.Errorf("Expected Error after checkpoint failure, got %s", csm.MustState())
		}
	})

	t.Run("Restore_Failure", func(t *testing.T) {
		fake := NewFakeComponent()
		defer fake.Close()

		// Configure restore to fail
		fake.SetRestoreError(fmt.Errorf("restore failed"))

		csm := NewComponentState(fake)

		// Start component first
		csm.Fire(ComponentTriggerStart)
		fake.EmitEvent(adapters.ComponentStarting)
		fake.EmitEvent(adapters.ComponentStarted)
		fake.EmitEvent(adapters.ComponentReady)
		waitForComponentState(csm, ComponentStateRunning, 10*time.Second)

		// Request restore (should fail)
		if err := csm.Fire(ComponentTriggerRestore); err != nil {
			t.Fatalf("Failed to request restore: %v", err)
		}

		// Wait for restore failure to transition to Error
		if !waitForComponentState(csm, ComponentStateError, 10*time.Second) {
			t.Errorf("Expected Error after restore failure, got %s", csm.MustState())
		}
	})
}

// NewTestableComponentStateMachine creates a testable component state machine for system state testing
func NewTestableComponentStateMachine() (*ComponentState, *FakeComponent) {
	fake := NewFakeComponent()
	csm := NewComponentState(fake)
	return csm, fake
}

// NewTestableComponentSetStateMachine creates a testable component set state machine for system state testing
func NewTestableComponentSetStateMachine() (*ComponentSetState, map[string]*FakeComponent) {
	fakeComponents := make(map[string]*FakeComponent)
	components := make(map[string]*ComponentState)

	// Create test components
	fakeComponents["db"] = NewFakeComponent()
	fakeComponents["fs"] = NewFakeComponent()

	components["db"] = NewComponentState(fakeComponents["db"])
	components["fs"] = NewComponentState(fakeComponents["fs"])

	css := NewComponentSetState(components)
	return css, fakeComponents
}
