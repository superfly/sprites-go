package managers

import (
	"context"
	"fmt"
	"testing"

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
	shouldFailStart      bool
	shouldFailCheckpoint bool
	shouldFailRestore    bool
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

func (tmc *testManagedComponent) Checkpoint() error {
	tmc.checkpointCalls++
	if tmc.shouldFailCheckpoint {
		return fmt.Errorf("checkpoint failed")
	}
	// Don't send events automatically for table-driven tests
	return nil
}

func (tmc *testManagedComponent) Restore() error {
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
		{"Direct transitions", []string{"Starting", "Running", "Stopping", "Stopped"}, []string{"Starting", "Running", "Stopping", "Stopped"}, "Stopped", true, false, ""},
		{"Checkpoint transition", []string{"Starting", "Running", "Checkpointing", "Running"}, []string{"Starting", "Running", "Checkpointing", "Running"}, "Running", true, false, ""},
		{"Restore transition", []string{"Starting", "Running", "Restoring", "Running"}, []string{"Starting", "Running", "Restoring", "Running"}, "Running", true, false, ""},
		{"Direct error", []string{"Error"}, []string{"Error"}, "Error", false, false, ""},

		// Custom initial states
		{"From Running state", []string{"Stopping", "Stopped"}, []string{"Stopping", "Stopped"}, "Stopped", true, false, "Running"},

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
				csm = NewComponentState("TestComponent", component, nil, tt.initialState)
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
