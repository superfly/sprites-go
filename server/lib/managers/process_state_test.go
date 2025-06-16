package managers

import (
	"context"
	"fmt"
	"os"
	"testing"
	"time"

	"sprite-env/lib/adapters"

	"github.com/qmuntal/stateless"
)

// testManagedProcess implements ManagedProcess for testing
type testManagedProcess struct {
	startCalls      int
	stopCalls       int
	signalCalls     int
	lastSignal      os.Signal
	eventsCh        chan adapters.ProcessEventType
	shouldFailStart bool // Control whether Start() fails
}

func newTestManagedProcess() *testManagedProcess {
	return &testManagedProcess{
		eventsCh:        make(chan adapters.ProcessEventType, 10), // Buffered channel for testing
		shouldFailStart: true,                                     // Default to failing start for backward compatibility
	}
}

func newTestManagedProcessWithSuccessfulStart() *testManagedProcess {
	return &testManagedProcess{
		eventsCh:        make(chan adapters.ProcessEventType, 10),
		shouldFailStart: false, // This one can succeed
	}
}

func (tmp *testManagedProcess) Start(ctx context.Context) error {
	tmp.startCalls++
	if tmp.shouldFailStart {
		// Return error to simulate start failure
		return fmt.Errorf("start failed")
	}

	// Simulate successful start by triggering Started event
	go func() {
		time.Sleep(time.Millisecond)
		tmp.eventsCh <- adapters.ProcessStartedEvent
	}()

	return nil
}

func (tmp *testManagedProcess) Stop() {
	tmp.stopCalls++
	// Simulate async stop completion
	go func() {
		time.Sleep(time.Millisecond) // Small delay for deterministic testing
		tmp.eventsCh <- adapters.ProcessStoppedEvent
	}()
}

func (tmp *testManagedProcess) Signal(sig os.Signal) {
	tmp.signalCalls++
	tmp.lastSignal = sig
	// Simulate async signal handling
	go func() {
		time.Sleep(time.Millisecond) // Small delay for deterministic testing
		tmp.eventsCh <- adapters.ProcessSignaledEvent
	}()
}

func (tmp *testManagedProcess) Events() <-chan adapters.ProcessEventType {
	return tmp.eventsCh
}

// Helper methods for testing
func (tmp *testManagedProcess) getStartCalls() int {
	return tmp.startCalls
}

func (tmp *testManagedProcess) getStopCalls() int {
	return tmp.stopCalls
}

func (tmp *testManagedProcess) getSignalCalls() int {
	return tmp.signalCalls
}

func (tmp *testManagedProcess) getLastSignal() os.Signal {
	return tmp.lastSignal
}

// Trigger events manually for testing crashes
func (tmp *testManagedProcess) triggerCrashed() {
	tmp.eventsCh <- adapters.ProcessFailedEvent
}

func (tmp *testManagedProcess) triggerExited() {
	tmp.eventsCh <- adapters.ProcessExitedEvent
}

func (tmp *testManagedProcess) triggerStarted() {
	tmp.eventsCh <- adapters.ProcessStartedEvent
}

func TestProcessStateManager_ManagedProcessIntegration(t *testing.T) {
	t.Run("Starting state start failure transitions to Error", func(t *testing.T) {
		process := newTestManagedProcess()
		psm := NewProcessState(ProcessStateConfig{Process: process}, nil)
		defer psm.Close()

		var stateChanges []string
		psm.OnTransitioned(func(ctx context.Context, transition stateless.Transition) {
			stateChanges = append(stateChanges, transition.Destination.(string))
		})

		// Fire Starting - should call Start on process which will fail and transition to Error
		err := psm.Fire("Starting")
		if err != nil {
			t.Fatalf("Failed to fire Starting: %v", err)
		}

		// Give time for the error transition to happen
		time.Sleep(10 * time.Millisecond)

		// Verify process.Start was called
		if process.getStartCalls() != 1 {
			t.Errorf("Expected 1 Start call, got %d", process.getStartCalls())
		}

		// Verify state changes: should be [Starting, Error] since Start() failed
		expectedStates := []string{"Starting", "Error"}
		if len(stateChanges) != len(expectedStates) {
			t.Errorf("Expected %v state changes, got %v", expectedStates, stateChanges)
		}
	})

	t.Run("Stopping state triggers process stop", func(t *testing.T) {
		process := newTestManagedProcessWithSuccessfulStart()
		psm := NewProcessState(ProcessStateConfig{Process: process}, nil)
		defer psm.Close()

		var stateChanges []string
		psm.OnTransitioned(func(ctx context.Context, transition stateless.Transition) {
			stateChanges = append(stateChanges, transition.Destination.(string))
		})

		// Fire Starting - this should succeed and automatically trigger Running
		err := psm.Fire("Starting")
		if err != nil {
			t.Fatalf("Failed to fire Starting: %v", err)
		}

		// Wait for the Started event to trigger Running transition
		time.Sleep(10 * time.Millisecond)

		// Fire Stopping - should call Stop on process and transition to Stopped
		err = psm.Fire("Stopping")
		if err != nil {
			t.Fatalf("Failed to fire Stopping: %v", err)
		}

		// Give event listener time to execute
		time.Sleep(20 * time.Millisecond)

		// Verify process.Stop was called
		if process.getStopCalls() != 1 {
			t.Errorf("Expected 1 Stop call, got %d", process.getStopCalls())
		}

		// Verify final state is Stopped
		currentState := psm.MustState().(string)
		if currentState != "Stopped" {
			t.Errorf("Expected final state to be Stopped, got %s", currentState)
		}
	})

	t.Run("Signaling state triggers process signal", func(t *testing.T) {
		process := newTestManagedProcessWithSuccessfulStart()
		psm := NewProcessState(ProcessStateConfig{Process: process}, nil)
		defer psm.Close()

		// Fire Starting to get to Running state
		psm.Fire("Starting")
		time.Sleep(10 * time.Millisecond) // Wait for Running transition

		// Fire Signaling - should call Signal on process
		err := psm.Fire("Signaling")
		if err != nil {
			t.Fatalf("Failed to fire Signaling: %v", err)
		}

		// Give time for signal to be processed
		time.Sleep(10 * time.Millisecond)

		// Verify process.Signal was called
		if process.getSignalCalls() != 1 {
			t.Errorf("Expected 1 Signal call, got %d", process.getSignalCalls())
		}

		// Verify signal was os.Interrupt
		if process.getLastSignal() != os.Interrupt {
			t.Errorf("Expected os.Interrupt signal, got %v", process.getLastSignal())
		}
	})

	t.Run("Process events trigger state transitions", func(t *testing.T) {
		process := newTestManagedProcessWithSuccessfulStart()
		psm := NewProcessState(ProcessStateConfig{Process: process}, nil)
		defer psm.Close()

		var stateChanges []string
		psm.OnTransitioned(func(ctx context.Context, transition stateless.Transition) {
			stateChanges = append(stateChanges, transition.Destination.(string))
		})

		// Fire Starting to get to Running state
		psm.Fire("Starting")
		time.Sleep(10 * time.Millisecond) // Wait for Running transition

		// Manually trigger Exited event - should transition to Exited
		process.triggerExited()
		time.Sleep(5 * time.Millisecond)

		// Verify state changes: should include Starting, Running, and Exited
		expectedToContain := []string{"Starting", "Running", "Exited"}
		for _, expected := range expectedToContain {
			found := false
			for _, actual := range stateChanges {
				if actual == expected {
					found = true
					break
				}
			}
			if !found {
				t.Errorf("Expected state changes to contain %s, got %v", expected, stateChanges)
			}
		}
	})

	t.Run("Process crashes trigger error state", func(t *testing.T) {
		process := newTestManagedProcessWithSuccessfulStart()
		psm := NewProcessState(ProcessStateConfig{Process: process}, nil)
		defer psm.Close()

		var stateChanges []string
		psm.OnTransitioned(func(ctx context.Context, transition stateless.Transition) {
			stateChanges = append(stateChanges, transition.Destination.(string))
		})

		// Fire Starting to get to Running state
		psm.Fire("Starting")
		time.Sleep(10 * time.Millisecond) // Wait for Running transition

		// Manually trigger a crash - should transition to Error
		process.triggerCrashed()
		time.Sleep(5 * time.Millisecond)

		// Verify state changes include Starting, Running, and Error
		expectedToContain := []string{"Starting", "Running", "Error"}
		for _, expected := range expectedToContain {
			found := false
			for _, actual := range stateChanges {
				if actual == expected {
					found = true
					break
				}
			}
			if !found {
				t.Errorf("Expected state changes to contain %s, got %v", expected, stateChanges)
			}
		}
	})
}

func TestProcessStateManager_ValidSequences(t *testing.T) {
	tests := []struct {
		name                 string
		sequence             []string
		shouldSucceed        bool
		needsSuccessfulStart bool // Some tests need successful start behavior
	}{
		// Valid complete lifecycles
		{
			name:                 "Normal startup and shutdown",
			sequence:             []string{"Starting", "Running", "Stopping", "Stopped"},
			shouldSucceed:        true,
			needsSuccessfulStart: true,
		},
		{
			name:                 "Normal startup and permanent stop",
			sequence:             []string{"Starting", "Running", "Stopping", "Stopped"},
			shouldSucceed:        true,
			needsSuccessfulStart: true,
		},
		{
			name:                 "Startup then signal and kill",
			sequence:             []string{"Starting", "Running", "Signaling", "Killed"},
			shouldSucceed:        true,
			needsSuccessfulStart: true,
		},
		{
			name:                 "Normal stop sequence",
			sequence:             []string{"Starting", "Running", "Stopping", "Stopped"},
			shouldSucceed:        true,
			needsSuccessfulStart: true,
		},
		{
			name:                 "Full stop sequence",
			sequence:             []string{"Starting", "Running", "Stopping", "Stopped"},
			shouldSucceed:        true,
			needsSuccessfulStart: true,
		},
		{
			name:          "Early initialization error",
			sequence:      []string{"Error"},
			shouldSucceed: true,
		},
		{
			name:          "Startup error",
			sequence:      []string{"Starting", "Error"},
			shouldSucceed: true,
		},
		{
			name:                 "Runtime crash",
			sequence:             []string{"Starting", "Running", "Crashed"},
			shouldSucceed:        true,
			needsSuccessfulStart: true,
		},
		{
			name:                 "Process exits normally",
			sequence:             []string{"Starting", "Running", "Exited"},
			shouldSucceed:        true,
			needsSuccessfulStart: true,
		},
		{
			name:                 "Error during stop",
			sequence:             []string{"Starting", "Running", "Stopping", "Error"},
			shouldSucceed:        true,
			needsSuccessfulStart: true,
		},
		{
			name:                 "Killed during stop",
			sequence:             []string{"Starting", "Running", "Stopping", "Killed"},
			shouldSucceed:        true,
			needsSuccessfulStart: true,
		},
		{
			name:                 "Error during stop",
			sequence:             []string{"Starting", "Running", "Stopping", "Error"},
			shouldSucceed:        true,
			needsSuccessfulStart: true,
		},
		{
			name:                 "Killed during stop",
			sequence:             []string{"Starting", "Running", "Stopping", "Killed"},
			shouldSucceed:        true,
			needsSuccessfulStart: true,
		},

		// Invalid sequences - should fail at specific points
		{
			name:          "Skip Starting phase",
			sequence:      []string{"Running"},
			shouldSucceed: false,
		},
		{
			name:          "Skip Running phase",
			sequence:      []string{"Starting", "Stopping"},
			shouldSucceed: false,
		},
		{
			name:          "Direct to terminal from init",
			sequence:      []string{"Stopped"},
			shouldSucceed: false,
		},
		{
			name:          "Direct to crash from init",
			sequence:      []string{"Crashed"},
			shouldSucceed: false,
		},
		{
			name:                 "Backwards to Starting from Running",
			sequence:             []string{"Starting", "Running", "Starting"},
			shouldSucceed:        false,
			needsSuccessfulStart: true,
		},
		{
			name:          "Backwards to Initializing from Starting",
			sequence:      []string{"Starting", "Initializing"},
			shouldSucceed: false,
		},
		{
			name:          "Terminal state escape - Error",
			sequence:      []string{"Starting", "Error", "Running"},
			shouldSucceed: false,
		},
		{
			name:                 "Terminal state escape - Crashed",
			sequence:             []string{"Starting", "Running", "Crashed", "Starting"},
			shouldSucceed:        false,
			needsSuccessfulStart: true,
		},
		{
			name:                 "Terminal state escape - Killed",
			sequence:             []string{"Starting", "Running", "Killed", "Running"},
			shouldSucceed:        false,
			needsSuccessfulStart: true,
		},
		{
			name:                 "Terminal state escape - Exited",
			sequence:             []string{"Starting", "Running", "Exited", "Initializing"},
			shouldSucceed:        false,
			needsSuccessfulStart: true,
		},
		{
			name:                 "Invalid escape from Stopped to Running",
			sequence:             []string{"Starting", "Running", "Stopping", "Stopped", "Running"},
			shouldSucceed:        false,
			needsSuccessfulStart: true,
		},
		{
			name:                 "Invalid escape from Stopped to Initializing",
			sequence:             []string{"Starting", "Running", "Stopping", "Stopped", "Initializing"},
			shouldSucceed:        false,
			needsSuccessfulStart: true,
		},
		{
			name:                 "Invalid escape from Stopped to Starting",
			sequence:             []string{"Starting", "Running", "Stopping", "Stopped", "Starting"},
			shouldSucceed:        false,
			needsSuccessfulStart: true,
		},
		{
			name:                 "Invalid escape from Stopped to Starting",
			sequence:             []string{"Starting", "Running", "Stopping", "Stopped", "Starting"},
			shouldSucceed:        false,
			needsSuccessfulStart: true,
		},
		{
			name:                 "Invalid escape from Stopped to Running",
			sequence:             []string{"Starting", "Running", "Stopping", "Stopped", "Running"},
			shouldSucceed:        false,
			needsSuccessfulStart: true,
		},
		{
			name:                 "Invalid escape from Stopped to Initializing",
			sequence:             []string{"Starting", "Running", "Stopping", "Stopped", "Initializing"},
			shouldSucceed:        false,
			needsSuccessfulStart: true,
		},
		{
			name:                 "Skip stop phase",
			sequence:             []string{"Starting", "Running", "Stopped"},
			shouldSucceed:        false,
			needsSuccessfulStart: true,
		},
		{
			name:                 "Skip stop phase",
			sequence:             []string{"Starting", "Running", "Stopped"},
			shouldSucceed:        false,
			needsSuccessfulStart: true,
		},
		{
			name:                 "Invalid transition from Stopping to Error",
			sequence:             []string{"Starting", "Running", "Stopping", "Error"},
			shouldSucceed:        true,
			needsSuccessfulStart: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			var process *testManagedProcess
			var psm *ProcessState

			if tt.needsSuccessfulStart {
				process = newTestManagedProcessWithSuccessfulStart()
				psm = NewProcessState(ProcessStateConfig{Process: process}, nil)
			} else {
				// Use no process for pure state machine testing
				psm = NewProcessState(ProcessStateConfig{Process: nil}, nil)
			}
			defer psm.Close()

			// Track how far we got in the sequence
			var lastSuccessfulState string = "Initializing"

			for i, state := range tt.sequence {
				// Skip "Running" if we automatically transitioned to it from "Starting"
				if state == "Running" && tt.needsSuccessfulStart {
					currentState := psm.MustState().(string)
					if currentState == "Running" {
						// We're already in Running state due to automatic transition, skip this step
						lastSuccessfulState = "Running"
						continue
					}
				}

				err := psm.Fire(state)

				// For Starting state with successful process, wait for automatic transition
				if state == "Starting" && tt.needsSuccessfulStart && err == nil {
					time.Sleep(5 * time.Millisecond) // Wait for Started event
				}

				if tt.shouldSucceed {
					// For valid sequences, all transitions should work
					if err != nil {
						t.Fatalf("Step %d: Failed to transition to %s: %v", i+1, state, err)
					}

					currentState := psm.MustState().(string)
					// For Starting with successful process, expect it to go to Running automatically
					expectedState := state
					if state == "Starting" && tt.needsSuccessfulStart {
						expectedState = "Running" // Should automatically transition
					}

					if currentState != expectedState {
						t.Fatalf("Step %d: Expected state %s, got %s", i+1, expectedState, currentState)
					}
					lastSuccessfulState = currentState
				} else {
					// For invalid sequences, we expect it to fail at some point
					if err != nil {
						// Good! It failed as expected. Verify state didn't change.
						currentState := psm.MustState().(string)
						if currentState != lastSuccessfulState {
							t.Errorf("State changed to %s even though transition should have failed", currentState)
						}
						return // Test passed - sequence failed as expected
					}
					// If no error, update our tracking
					currentState := psm.MustState().(string)
					if currentState == state {
						lastSuccessfulState = state
					} else if state == "Starting" && tt.needsSuccessfulStart && currentState == "Running" {
						lastSuccessfulState = "Running" // Auto-transition happened
					}
				}
			}

			// If we get here with shouldSucceed=false, the sequence didn't fail
			if !tt.shouldSucceed {
				t.Errorf("Expected sequence to fail, but all transitions succeeded")
			}
		})
	}
}

func TestProcessStateManager_InitialState(t *testing.T) {
	process := newTestManagedProcess()
	psm := NewProcessState(ProcessStateConfig{Process: process}, nil)
	defer psm.Close()

	initialState := psm.MustState().(string)
	expectedState := "Initializing"

	if initialState != expectedState {
		t.Errorf("Expected initial state to be %s, got %s", expectedState, initialState)
	}
}

func TestProcessStateManager_TLASpecCompliance(t *testing.T) {
	t.Run("Process starts in Initializing state", func(t *testing.T) {
		process := newTestManagedProcess()
		psm := NewProcessState(ProcessStateConfig{Process: process}, nil)
		defer psm.Close()

		state := psm.MustState().(string)
		if state != "Initializing" {
			t.Errorf("Process should start in Initializing state, got %s", state)
		}
	})

	t.Run("Terminal states are truly terminal", func(t *testing.T) {
		terminalStates := []string{"Error", "Crashed", "Killed", "Exited", "Stopped"}

		for _, terminalState := range terminalStates {
			process := newTestManagedProcessWithSuccessfulStart()
			psm := NewProcessState(ProcessStateConfig{Process: process}, nil)
			defer psm.Close()

			// Get to terminal state
			err := psm.Fire("Starting")
			if err != nil {
				t.Fatalf("Failed to go to Starting: %v", err)
			}
			// Wait for automatic Running transition
			time.Sleep(5 * time.Millisecond)

			// Special handling for terminal states that require specific paths
			if terminalState == "Stopped" {
				err = psm.Fire("Stopping")
				if err != nil {
					t.Fatalf("Failed to reach Stopping: %v", err)
				}
				// Wait for automatic transition to Stopped - no manual fire needed
				time.Sleep(10 * time.Millisecond)
				currentState := psm.MustState().(string)
				if currentState != "Stopped" {
					t.Fatalf("Expected automatic transition to Stopped, got %s", currentState)
				}
			} else {
				err = psm.Fire(terminalState)
				if err != nil {
					t.Fatalf("Failed to reach terminal state %s: %v", terminalState, err)
				}
			}

			// Try to escape - should all fail
			escapeAttempts := []string{"Running", "Starting", "Initializing", "Stopped"}
			for _, escapeState := range escapeAttempts {
				err := psm.Fire(escapeState)
				if err == nil {
					t.Errorf("Terminal state %s should not allow transition to %s", terminalState, escapeState)
				}
			}
		}
	})

	t.Run("Terminal states cannot be escaped", func(t *testing.T) {
		// Test that Stopped is truly terminal - no transitions out allowed
		process := newTestManagedProcessWithSuccessfulStart()
		psm := NewProcessState(ProcessStateConfig{Process: process}, nil)
		defer psm.Close()

		// Get to Stopped state
		sequence := []string{"Starting", "Stopping"}
		for _, state := range sequence {
			err := psm.Fire(state)
			if err != nil {
				t.Fatalf("Failed to reach Stopped state at %s: %v", state, err)
			}
			// Wait for automatic transitions
			if state == "Starting" {
				time.Sleep(5 * time.Millisecond)
			}
		}

		// Wait for automatic transition to Stopped after Stopping
		time.Sleep(10 * time.Millisecond)
		currentState := psm.MustState().(string)
		if currentState != "Stopped" {
			t.Fatalf("Expected automatic transition to Stopped, got %s", currentState)
		}

		// Verify that Stopped is terminal - no escape attempts should succeed
		invalidEscapes := []string{"Initializing", "Starting", "Running"}
		for _, escapeState := range invalidEscapes {
			err := psm.Fire(escapeState)
			if err == nil {
				t.Errorf("Stopped state should not allow transition to %s", escapeState)
			}
		}

	})

	t.Run("Component lifecycle matches TLA+ ComponentTransition", func(t *testing.T) {
		// Test the basic component lifecycle from TLA+ spec
		process := newTestManagedProcessWithSuccessfulStart()
		psm := NewProcessState(ProcessStateConfig{Process: process}, nil)
		defer psm.Close()

		// ComponentTransition: Initializing -> Starting -> Running (auto) -> Stopping -> Stopped
		lifecycle := []string{"Starting", "Stopping"}

		for _, state := range lifecycle {
			err := psm.Fire(state)
			if err != nil {
				t.Fatalf("Failed TLA+ component lifecycle at %s: %v", state, err)
			}

			// For Starting, wait for automatic transition to Running
			if state == "Starting" {
				time.Sleep(5 * time.Millisecond)
				currentState := psm.MustState().(string)
				if currentState != "Running" {
					t.Fatalf("Expected automatic transition to Running after Starting, got %s", currentState)
				}
			}
		}

		// Wait for automatic transition to Stopped after Stopping
		time.Sleep(10 * time.Millisecond)
		currentState := psm.MustState().(string)
		if currentState != "Stopped" {
			t.Fatalf("Expected automatic transition to Stopped after Stopping, got %s", currentState)
		}
	})
}
