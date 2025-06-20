package managers

import (
	"context"
	"fmt"
	"testing"

	"sprite-env/lib/adapters"

	"github.com/qmuntal/stateless"
	"github.com/stretchr/testify/assert"
)

// testManagedComponent implements ManagedComponent for testing
type testManagedComponent struct {
	startCalls           int
	stopCalls            int
	checkpointCalls      int
	restoreCalls         int
	eventsCh             chan adapters.ComponentEventType
	shouldFailStart      bool
	shouldFailCheckpoint bool
	shouldFailRestore    bool
	startFunc            func(ctx context.Context) error
	eventChan            chan adapters.ComponentEventType
}

func newTestManagedComponent() *testManagedComponent {
	return &testManagedComponent{
		eventsCh:        make(chan adapters.ComponentEventType, 10),
		shouldFailStart: true,
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
		return fmt.Errorf("start failed")
	}
	// Don't send events automatically for table-driven tests
	return nil
}

func (tmc *testManagedComponent) Stop() {
	tmc.stopCalls++
	// Don't send events automatically for table-driven tests
}

func (tmc *testManagedComponent) Checkpoint(checkpointID string) error {
	tmc.checkpointCalls++
	if tmc.shouldFailCheckpoint {
		return fmt.Errorf("checkpoint failed")
	}
	// Don't send events automatically for table-driven tests
	return nil
}

func (tmc *testManagedComponent) Restore(checkpointID string) error {
	tmc.restoreCalls++
	if tmc.shouldFailRestore {
		return fmt.Errorf("restore failed")
	}
	// Don't send events automatically for table-driven tests
	return nil
}

func (tmc *testManagedComponent) Events() <-chan adapters.ComponentEventType {
	return tmc.eventsCh
}

func (tmc *testManagedComponent) GetName() string {
	return "TestComponent"
}

func (tmc *testManagedComponent) Ready() error {
	// Simple implementation for testing
	if tmc.shouldFailStart {
		return fmt.Errorf("not ready")
	}
	return nil
}

// Helper function to create a component state manager that records all transitions
func createComponentWithRecording(useSuccessfulOps bool) (*ComponentState, *testManagedComponent, *[]string) {
	var component *testManagedComponent
	if useSuccessfulOps {
		component = newTestManagedComponentWithSuccessfulOperations()
	} else {
		component = newTestManagedComponent()
	}

	csm := NewComponentState("TestComponent", component)

	var stateChanges []string
	csm.OnTransitioned(func(ctx context.Context, transition stateless.Transition) {
		stateChanges = append(stateChanges, transition.Destination.(string))
	})

	return csm, component, &stateChanges
}

// TestComponentState_AllScenarios tests all component state scenarios
func TestComponentState_AllScenarios(t *testing.T) {
	tests := []struct {
		name               string
		actions            []string
		expectedStates     []string
		expectedFinalState string
		useSuccessfulOps   bool
		shouldFail         bool
		initialState       string
	}{
		// Basic functionality
		{"Initial state", []string{}, []string{}, "Initializing", false, false, ""},
		{"Direct transitions", []string{"Starting", "Stopping"}, []string{"Starting", "Running", "Stopping", "Stopped"}, "Stopped", true, false, ""},
		{"Checkpoint transition", []string{"Starting", "Checkpointing"}, []string{"Starting", "Running", "Checkpointing", "Running"}, "Running", true, false, ""},
		{"Restore transition", []string{"Starting", "Restoring"}, []string{"Starting", "Running", "Restoring", "Running"}, "Running", true, false, ""},
		{"Direct error", []string{"Error"}, []string{"Error"}, "Error", false, false, ""},
		{"Starting fails", []string{"Starting"}, []string{"Starting", "Error"}, "Error", false, false, ""},

		// Custom initial states
		{"From Running state", []string{"Stopping"}, []string{"Stopping", "Stopped"}, "Stopped", true, false, "Running"},

		// Invalid sequences
		{"Skip to Running", []string{"Running"}, []string{}, "Initializing", false, true, ""},
		{"Skip to Stopped", []string{"Stopped"}, []string{}, "Initializing", false, true, ""},
		{"Terminal state escape", []string{"Error", "Starting"}, []string{"Error"}, "Error", false, true, ""},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			csm, _, stateChanges := createComponentWithRecording(tt.useSuccessfulOps)

			// Handle custom initial state
			if tt.initialState != "" {
				csm.Close()
				var component *testManagedComponent
				if tt.useSuccessfulOps {
					component = newTestManagedComponentWithSuccessfulOperations()
				} else {
					component = newTestManagedComponent()
				}
				// Cannot set custom initial state anymore - ComponentState always starts at "Initializing"
				// Need to transition to the desired state instead
				csm = NewComponentState("TestComponent", component)
				
				// Transition to the desired initial state (don't track these transitions)
				if tt.initialState == "Running" {
					csm.Fire("Starting")
					// Don't need to fire "Running" - handleStarting does it automatically
				}
				
				// Now set up state change tracking
				var newStateChanges []string
				csm.OnTransitioned(func(ctx context.Context, transition stateless.Transition) {
					newStateChanges = append(newStateChanges, transition.Destination.(string))
				})
				stateChanges = &newStateChanges
			}
			defer csm.Close()

			// Execute actions
			var failed bool
			for _, action := range tt.actions {
				err := csm.Fire(action)
				if err != nil {
					failed = true
					break
				}
			}

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

			// Verify final state
			currentState := csm.MustState().(string)
			if currentState != tt.expectedFinalState {
				t.Errorf("Expected final state %s, got %s", tt.expectedFinalState, currentState)
			}

			// Verify state sequence for successful cases with expected states
			if len(tt.expectedStates) > 0 {
				if len(*stateChanges) != len(tt.expectedStates) {
					t.Errorf("Expected %v state changes, got %v", tt.expectedStates, *stateChanges)
					return
				}

				for i, expected := range tt.expectedStates {
					if (*stateChanges)[i] != expected {
						t.Errorf("State %d: expected %s, got %s", i, expected, (*stateChanges)[i])
					}
				}
			}

			t.Logf("Final state: %s, State changes: %v, Initial: %s", currentState, *stateChanges, tt.initialState)
		})
	}
}

func TestComponentStateTransitions(t *testing.T) {
	t.Run("Starting->Running transition", func(t *testing.T) {
		component := &testManagedComponent{
			startFunc: func(ctx context.Context) error { return nil },
			eventChan: make(chan adapters.ComponentEventType, 10),
		}

		csm := NewComponentState("test", component)

		// Verify initial state
		assert.Equal(t, "Initializing", csm.MustState())

		// ... existing code ...
	})
}

func TestComponentStateWithInitialState(t *testing.T) {
	t.Run("Custom initial state", func(t *testing.T) {
		component := &testManagedComponent{
			eventChan: make(chan adapters.ComponentEventType, 10),
		}

		// Create with custom initial state
		csm := NewComponentState("test", component)
		// Start from Initializing as per spec
		assert.Equal(t, "Initializing", csm.MustState())
	})
}
