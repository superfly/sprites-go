package managers

import (
	"context"
	"fmt"
	"os"
	"testing"

	"sprite-env/lib/adapters"
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
		return fmt.Errorf("start failed")
	}
	// Don't send events automatically for table-driven tests
	return nil
}

func (tmp *testManagedProcess) Stop() {
	tmp.stopCalls++
	// Don't send events automatically for table-driven tests
}

func (tmp *testManagedProcess) Signal(sig os.Signal) {
	tmp.signalCalls++
	tmp.lastSignal = sig
	// Don't send events automatically for table-driven tests
}

func (tmp *testManagedProcess) Events() <-chan adapters.ProcessEventType {
	return tmp.eventsCh
}

func (tmp *testManagedProcess) GetState() string {
	// Simple implementation for testing
	return "stopped"
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

// TestProcessStateManager_ValidSequences tests all process state scenarios
func TestProcessStateManager_ValidSequences(t *testing.T) {
	tests := []struct {
		name               string
		sequence           []string
		expectedFinalState string
		shouldSucceed      bool
		initialState       string
	}{
		// Basic functionality
		{"Initial state", []string{}, "Initializing", true, ""},
		{"Normal startup sequence", []string{"Starting"}, "Starting", true, ""}, // Stays in Starting without ProcessStartedEvent
		{"Direct to Error", []string{"ProcessError"}, "Error", true, ""},
		{"Partial shutdown sequence", []string{"Starting", "ProcessRunning", "Stopping"}, "Stopped", true, ""}, // Automatically goes to Stopped because test process returns "stopped"

		// Custom initial states
		{"From Starting state", []string{"ProcessRunning"}, "Running", true, "Starting"},

		// Invalid transitions
		{"Skip Starting phase", []string{"ProcessRunning"}, "Initializing", false, ""},
		{"Direct to Stopped from init", []string{"ProcessStopped"}, "Initializing", false, ""},
		{"Stopping from Initializing", []string{"Stopping"}, "Initializing", false, ""},
		{"Backwards transition", []string{"Starting", "Initializing"}, "Starting", false, ""},
		{"Terminal state escape", []string{"ProcessError", "ProcessRunning"}, "Error", false, ""},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			var psm *ProcessState

			// Use actual test process that doesn't send automatic events
			process := newTestManagedProcessWithSuccessfulStart()
			config := ProcessStateConfig{Process: process}
			if tt.initialState != "" {
				config.InitialState = tt.initialState
			}
			psm = NewProcessState(config)
			defer psm.Close()

			var lastError error
			for _, state := range tt.sequence {
				err := psm.Fire(state)
				if err != nil {
					lastError = err
					break
				}
			}

			// Verify success/failure expectations
			if tt.shouldSucceed {
				if lastError != nil {
					t.Errorf("Expected sequence to succeed, but failed: %v", lastError)
				}
			} else {
				if lastError == nil {
					t.Errorf("Expected sequence to fail, but succeeded")
				}
			}

			// Verify final state
			currentState := psm.MustState().(string)
			if currentState != tt.expectedFinalState {
				t.Errorf("Expected final state %s, got %s", tt.expectedFinalState, currentState)
			}

			t.Logf("Final state: %s, Initial: %s", currentState, tt.initialState)
		})
	}
}
