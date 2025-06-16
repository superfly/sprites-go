package managers

import (
	"testing"
)

// TestComponentGroupState_AllScenarios tests all component group state scenarios
func TestComponentGroupState_AllScenarios(t *testing.T) {
	tests := []struct {
		name               string
		componentFailures  []bool
		sequence           []string
		expectedFinalState string
		shouldSucceed      bool
	}{
		{
			name:               "Initial state",
			componentFailures:  []bool{false, false},
			sequence:           []string{},
			expectedFinalState: "Initializing",
			shouldSucceed:      true,
		},
		{
			name:               "Direct to Starting",
			componentFailures:  []bool{false, false, false},
			sequence:           []string{"Starting"},
			expectedFinalState: "Starting",
			shouldSucceed:      true,
		},
		{
			name:               "Component startup sequence",
			componentFailures:  []bool{false, false},
			sequence:           []string{"Starting", "Running"},
			expectedFinalState: "Running",
			shouldSucceed:      true,
		},
		{
			name:               "Full stop sequence",
			componentFailures:  []bool{false, false},
			sequence:           []string{"Starting", "Running", "Stopping", "Stopped"},
			expectedFinalState: "Stopped",
			shouldSucceed:      true,
		},
		{
			name:               "Invalid direct transition",
			componentFailures:  []bool{false, false},
			sequence:           []string{"Running"},
			expectedFinalState: "Initializing",
			shouldSucceed:      false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Create test components based on failure configuration
			var components []ManagedComponent
			for _, shouldFail := range tt.componentFailures {
				if shouldFail {
					components = append(components, newTestManagedComponent())
				} else {
					components = append(components, newTestManagedComponentWithSuccessfulOperations())
				}
			}

			config := ComponentGroupConfig{
				Components: components,
			}

			cgsm := NewComponentGroupState(config, nil)
			defer cgsm.Close()

			// Execute sequence
			var lastError error
			for _, trigger := range tt.sequence {
				err := cgsm.Fire(trigger)
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
			currentState := cgsm.MustState().(string)
			if currentState != tt.expectedFinalState {
				t.Errorf("Expected final state %s, got %s", tt.expectedFinalState, currentState)
			}

			t.Logf("Final state: %s", currentState)
		})
	}
}
