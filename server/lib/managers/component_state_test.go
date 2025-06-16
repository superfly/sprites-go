package managers

import (
	"context"
	"fmt"
	"testing"
	"time"

	"sprite-env/lib/adapters"

	"github.com/qmuntal/stateless"
)

// testManagedComponent implements ManagedComponent for testing
type testManagedComponent struct {
	startCalls           int
	stopCalls            int
	checkpointCalls      int
	restoreCalls         int
	eventsCh             chan adapters.ComponentEventType
	shouldFailStart      bool // Control whether Start() fails
	shouldFailCheckpoint bool // Control whether Checkpoint() fails
	shouldFailRestore    bool // Control whether Restore() fails
}

func newTestManagedComponent() *testManagedComponent {
	return &testManagedComponent{
		eventsCh:        make(chan adapters.ComponentEventType, 10), // Buffered channel for testing
		shouldFailStart: true,                                       // Default to failing start for backward compatibility
	}
}

func newTestManagedComponentWithSuccessfulOperations() *testManagedComponent {
	return &testManagedComponent{
		eventsCh:             make(chan adapters.ComponentEventType, 10),
		shouldFailStart:      false,
		shouldFailCheckpoint: false,
		shouldFailRestore:    false,
	}
}

func (tmc *testManagedComponent) Start(ctx context.Context) error {
	tmc.startCalls++
	if tmc.shouldFailStart {
		// Return error to simulate start failure
		return fmt.Errorf("start failed")
	}

	// Simulate successful start by triggering Started event, then Ready
	go func() {
		time.Sleep(time.Millisecond)
		tmc.eventsCh <- adapters.ComponentStarted
		time.Sleep(time.Millisecond)
		tmc.eventsCh <- adapters.ComponentReady
	}()

	return nil
}

func (tmc *testManagedComponent) Stop() {
	tmc.stopCalls++
	// Simulate async stop completion
	go func() {
		time.Sleep(time.Millisecond) // Small delay for deterministic testing
		tmc.eventsCh <- adapters.ComponentStopped
	}()
}

func (tmc *testManagedComponent) Checkpoint() error {
	tmc.checkpointCalls++
	if tmc.shouldFailCheckpoint {
		return fmt.Errorf("checkpoint failed")
	}

	// Simulate async checkpoint completion - use Ready since we don't have checkpointed
	go func() {
		time.Sleep(time.Millisecond)
		tmc.eventsCh <- adapters.ComponentReady
	}()

	return nil
}

func (tmc *testManagedComponent) Restore() error {
	tmc.restoreCalls++
	if tmc.shouldFailRestore {
		return fmt.Errorf("restore failed")
	}

	// Simulate async restore completion - use Ready since we don't have restored
	go func() {
		time.Sleep(time.Millisecond)
		tmc.eventsCh <- adapters.ComponentReady
	}()

	return nil
}

func (tmc *testManagedComponent) Events() <-chan adapters.ComponentEventType {
	return tmc.eventsCh
}

// GetName returns the component name for testing
func (tmc *testManagedComponent) GetName() string {
	return "TestComponent"
}

// Helper methods for testing
func (tmc *testManagedComponent) getStartCalls() int {
	return tmc.startCalls
}

func (tmc *testManagedComponent) getStopCalls() int {
	return tmc.stopCalls
}

func (tmc *testManagedComponent) getCheckpointCalls() int {
	return tmc.checkpointCalls
}

func (tmc *testManagedComponent) getRestoreCalls() int {
	return tmc.restoreCalls
}

// Trigger events manually for testing crashes
func (tmc *testManagedComponent) triggerCrashed() {
	tmc.eventsCh <- adapters.ComponentFailed
}

func (tmc *testManagedComponent) triggerStarted() {
	tmc.eventsCh <- adapters.ComponentStarted
}

// Helper function to create a component state manager that records all transitions
func createComponentWithRecording(useSuccessfulOps bool) (*ComponentState, *testManagedComponent, *[]string) {
	var component *testManagedComponent
	if useSuccessfulOps {
		component = newTestManagedComponentWithSuccessfulOperations()
	} else {
		component = newTestManagedComponent()
	}

	csm := NewComponentState("TestComponent", component, nil)

	var stateChanges []string
	csm.OnTransitioned(func(ctx context.Context, transition stateless.Transition) {
		stateChanges = append(stateChanges, transition.Destination.(string))
	})

	return csm, component, &stateChanges
}

func TestComponentState_Sequences(t *testing.T) {
	tests := []struct {
		name             string
		actions          []string
		expectedStates   []string
		useSuccessfulOps bool
		shouldFail       bool
	}{
		// Valid sequences
		{
			name:             "Normal startup and stop",
			actions:          []string{"Starting", "Stopping"},
			expectedStates:   []string{"Starting", "Running", "Stopping", "Stopped"},
			useSuccessfulOps: true,
		},
		{
			name:             "Checkpoint cycle",
			actions:          []string{"Starting", "Checkpointing"},
			expectedStates:   []string{"Starting", "Running", "Checkpointing", "Running"},
			useSuccessfulOps: true,
		},
		{
			name:             "Restore cycle",
			actions:          []string{"Starting", "Restoring"},
			expectedStates:   []string{"Starting", "Running", "Restoring", "Running"},
			useSuccessfulOps: true,
		},
		{
			name:             "Startup failure",
			actions:          []string{"Starting"},
			expectedStates:   []string{"Starting", "Error"},
			useSuccessfulOps: false,
		},
		{
			name:             "Direct error",
			actions:          []string{"Error"},
			expectedStates:   []string{"Error"},
			useSuccessfulOps: false,
		},

		// Invalid sequences
		{
			name:           "Skip to Running",
			actions:        []string{"Running"},
			expectedStates: []string{},
			shouldFail:     true,
		},
		{
			name:           "Skip to Stopped",
			actions:        []string{"Stopped"},
			expectedStates: []string{},
			shouldFail:     true,
		},
		{
			name:           "Backwards transition",
			actions:        []string{"Starting", "Initializing"},
			expectedStates: []string{"Starting", "Running"},
			shouldFail:     true,
		},
		{
			name:             "Checkpoint from wrong state",
			actions:          []string{"Starting", "Checkpointing"},
			expectedStates:   []string{"Starting"},
			shouldFail:       true,
			useSuccessfulOps: false, // Use failing start so we don't auto-transition to Running
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			csm, _, stateChanges := createComponentWithRecording(tt.useSuccessfulOps)
			defer csm.Close()

			// Execute actions
			var failed bool
			for _, action := range tt.actions {
				err := csm.Fire(action)
				if err != nil {
					failed = true
					break
				}
				time.Sleep(10 * time.Millisecond) // Let transitions complete
			}

			// Final wait
			time.Sleep(15 * time.Millisecond)

			if tt.shouldFail {
				if !failed {
					t.Errorf("Expected sequence to fail, but succeeded. States: %v", *stateChanges)
				}
				return
			}

			if failed {
				t.Errorf("Expected sequence to succeed, but failed. States: %v", *stateChanges)
				return
			}

			// Verify state sequence
			if len(*stateChanges) != len(tt.expectedStates) {
				t.Errorf("Expected %v state changes, got %v", tt.expectedStates, *stateChanges)
				return
			}

			for i, expected := range tt.expectedStates {
				if (*stateChanges)[i] != expected {
					t.Errorf("State %d: expected %s, got %s", i, expected, (*stateChanges)[i])
				}
			}
		})
	}
}

func TestComponentState_TerminalStates(t *testing.T) {
	terminalTests := []struct {
		name       string
		sequence   []string
		finalState string
	}{
		{
			name:       "Error terminal",
			sequence:   []string{"Error"},
			finalState: "Error",
		},
		{
			name:       "Stopped terminal",
			sequence:   []string{"Starting", "Stopping", "Stopped"},
			finalState: "Stopped",
		},
	}

	for _, tt := range terminalTests {
		t.Run(tt.name, func(t *testing.T) {
			csm, _, _ := createComponentWithRecording(true)
			defer csm.Close()

			// Execute sequence
			for _, action := range tt.sequence {
				csm.Fire(action)
				time.Sleep(10 * time.Millisecond)
			}

			// Verify final state
			if csm.MustState().(string) != tt.finalState {
				t.Errorf("Expected final state %s, got %s", tt.finalState, csm.MustState().(string))
			}

			// Try to escape - should fail
			escapeAttempts := []string{"Starting", "Running", "Initializing"}
			for _, escape := range escapeAttempts {
				err := csm.Fire(escape)
				if err == nil {
					t.Errorf("Terminal state %s should not allow transition to %s", tt.finalState, escape)
				}
			}
		})
	}
}

func TestComponentState_InitialState(t *testing.T) {
	csm, _, _ := createComponentWithRecording(false)
	defer csm.Close()

	if csm.MustState().(string) != "Initializing" {
		t.Errorf("Expected initial state Initializing, got %s", csm.MustState().(string))
	}
}
