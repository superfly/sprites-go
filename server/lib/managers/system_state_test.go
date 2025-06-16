package managers

import (
	"fmt"
	"testing"

	"sprite-env/lib/adapters"

	"github.com/stretchr/testify/require"
	"github.com/tj/assert"
)

// TestSystemStateManager_ComprehensiveTransitionMatrix tests state machine logic
func TestSystemStateManager_ComprehensiveTransitionMatrix(t *testing.T) {
	type TestStateSequence struct {
		Sequence           []string
		ExpectedFinalState string
		ShouldFail         bool
		FailurePoint       string
		InitialState       string // New field to test different initial states
	}

	sequences := []TestStateSequence{
		// Initial state test
		{[]string{}, "Initializing", false, "", ""},

		// Valid sequences from default initial state (Initializing)
		{[]string{"SystemStarting", "SystemReady", "ProcessRunning"}, "Running", false, "", ""},
		{[]string{"SystemStarting", "SystemReady"}, "Ready", false, "", ""},
		{[]string{"SystemStarting", "SystemReady", "ProcessRunning", "ComponentsStopping", "ComponentsStopped"}, "Stopped", false, "", ""},
		{[]string{"SystemStarting", "SystemReady", "ProcessError", "ProcessStopped"}, "Error", false, "", ""},
		{[]string{"SystemStarting", "ComponentsStopping", "ComponentsStopped"}, "Stopped", false, "", ""},
		{[]string{"SystemStarting", "SystemReady", "ProcessRunning", "ProcessCrashed", "ProcessStopped"}, "Error", false, "", ""},
		{[]string{"SystemStarting", "SystemReady", "ComponentsError"}, "Error", false, "", ""},

		// Sequences starting from different initial states (testing InitialState functionality)
		{[]string{"SystemReady", "ProcessRunning"}, "Running", false, "", "Starting"},
		{[]string{"ProcessRunning"}, "Running", false, "", "Ready"},
		{[]string{"ComponentsStopping", "ComponentsStopped"}, "Stopped", false, "", "Running"},
		{[]string{"ProcessError", "ProcessStopped"}, "Error", false, "", "Ready"},

		// Invalid sequences from default initial state
		{[]string{"SystemReady"}, "Initializing", true, "SystemReady", ""},
		{[]string{"SystemStarting", "ProcessRunning"}, "Starting", true, "ProcessRunning", ""},
		{[]string{"SystemStarting", "Initializing"}, "Starting", true, "Initializing", ""},
		{[]string{"SystemStarting", "SystemReady", "ProcessError", "ProcessStopped", "SystemStarting"}, "Error", true, "SystemStarting", ""},
		{[]string{"InvalidTrigger"}, "Initializing", true, "InvalidTrigger", ""},

		// Invalid sequences from custom initial states
		{[]string{"SystemStarting"}, "Ready", true, "SystemStarting", "Ready"},
		{[]string{"Initializing"}, "Running", true, "Initializing", "Running"},
	}

	for i, sequence := range sequences {
		t.Run(fmt.Sprintf("Sequence_%d", i+1), func(t *testing.T) {
			// Use custom initial state if specified
			var refs *EnhancedStateManagerRefs
			var stateChanges *[]string
			if sequence.InitialState != "" {
				systemConfig := &SystemConfig{InitialState: sequence.InitialState}
				refs, stateChanges = CreateEnhancedSystemWithAllManagersAndConfig(t, 2, true, nil, systemConfig)
			} else {
				refs, stateChanges = CreateEnhancedSystemWithAllManagers(t, 2, true, nil)
			}
			defer refs.Close()

			var lastError error
			for j, trigger := range sequence.Sequence {
				err := refs.System.Fire(trigger)
				if err != nil {
					lastError = err
					if sequence.ShouldFail && trigger == sequence.FailurePoint {
						break
					} else if !sequence.ShouldFail {
						t.Fatalf("Step %d (%s) failed unexpectedly: %v", j+1, trigger, err)
					}
				}
			}

			// Verify failure expectations
			if sequence.ShouldFail {
				if lastError == nil {
					t.Errorf("Expected sequence to fail at %s, but all transitions succeeded", sequence.FailurePoint)
				}
			} else {
				if lastError != nil {
					t.Errorf("Expected sequence to succeed, but failed: %v", lastError)
				}
			}

			// Verify final state
			currentState := refs.System.MustState().(string)
			if currentState != sequence.ExpectedFinalState {
				t.Errorf("Expected final state %s, got %s", sequence.ExpectedFinalState, currentState)
			}

			t.Logf("Final state: %s, State changes: %v, Initial: %s", currentState, *stateChanges, sequence.InitialState)
		})
	}
}

// TestSystemStateManager_Coordination tests coordination between state machines
func TestSystemStateManager_Coordination(t *testing.T) {
	tests := []struct {
		name           string
		initialState   string
		events         []string
		expectedState  string
		processState   *ProcessState
		componentState *ComponentGroupState
		checkProcess   func(t *testing.T, ps *ProcessState)
		checkComponent func(t *testing.T, cs *ComponentGroupState)
	}{
		{
			name:          "System startup coordination",
			initialState:  "Initializing",
			events:        []string{"SystemStarting"},
			expectedState: "Starting",
		},
		{
			name:          "Component success triggers process start",
			initialState:  "Starting",
			events:        []string{"ComponentsRunning"},
			expectedState: "Ready",
			processState:  NewProcessState(ProcessStateConfig{}, nil),
			checkProcess: func(t *testing.T, ps *ProcessState) {
				assert.Equal(t, "Starting", ps.MustState().(string))
			},
		},
		{
			name:          "Component failure triggers error recovery and process stop",
			initialState:  "Ready",
			events:        []string{"ComponentsErrorStopping"},
			expectedState: "ErrorRecovery",
			processState:  NewProcessState(ProcessStateConfig{}, nil),
			checkProcess: func(t *testing.T, ps *ProcessState) {
				assert.Equal(t, "Stopped", ps.MustState().(string))
			},
		},
		{
			name:          "Process stopped during error recovery triggers final error",
			initialState:  "ErrorRecovery",
			events:        []string{"ProcessStopped"},
			expectedState: "Error",
		},
		{
			name:          "Component failure from initializing state",
			initialState:  "Initializing",
			events:        []string{"SystemStarting", "ComponentsError"},
			expectedState: "Error",
		},
		{
			name:          "Process error triggers error recovery",
			initialState:  "Ready",
			events:        []string{"ProcessError"},
			expectedState: "ErrorRecovery",
			processState:  NewProcessState(ProcessStateConfig{}, nil),
			checkProcess: func(t *testing.T, ps *ProcessState) {
				assert.Equal(t, "Stopped", ps.MustState().(string))
			},
		},
		{
			name:          "System shutdown coordination",
			initialState:  "Running",
			events:        []string{"ComponentsStopping"},
			expectedState: "Stopped",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Create system state
			config := SystemConfig{
				ProcessState: tt.processState,
				InitialState: tt.initialState,
			}
			ss := NewSystemState(config, nil)

			// Fire events in sequence
			for _, event := range tt.events {
				require.NoError(t, ss.Fire(event))
			}

			// Check final state
			assert.Equal(t, tt.expectedState, ss.MustState().(string))

			// Check process state if needed
			if tt.checkProcess != nil {
				tt.checkProcess(t, tt.processState)
			}

			// Check component state if needed
			if tt.checkComponent != nil {
				tt.checkComponent(t, tt.componentState)
			}
		})
	}
}

func TestSystemStateTransitions(t *testing.T) {
	tests := []struct {
		name           string
		initialState   string
		event          string
		expectedState  string
		processState   *ProcessState
		componentState *ComponentGroupState
		checkProcess   func(t *testing.T, ps *ProcessState)
		checkComponent func(t *testing.T, cs *ComponentGroupState)
	}{
		{
			name:          "Initializing to Starting",
			initialState:  "Initializing",
			event:         "SystemStarting",
			expectedState: "Starting",
		},
		{
			name:          "Starting to Ready",
			initialState:  "Starting",
			event:         "ComponentsRunning",
			expectedState: "Ready",
		},
		{
			name:          "Ready to Running",
			initialState:  "Ready",
			event:         "ProcessRunning",
			expectedState: "Running",
		},
		{
			name:          "Running to ErrorRecovery on ComponentError",
			initialState:  "Running",
			event:         "ComponentsErrorStopping",
			expectedState: "ErrorRecovery",
			processState:  NewProcessState(ProcessStateConfig{}, nil),
			checkProcess: func(t *testing.T, ps *ProcessState) {
				assert.Equal(t, "Stopped", ps.MustState().(string))
			},
		},
		{
			name:          "ErrorRecovery to Error after ProcessStopped",
			initialState:  "ErrorRecovery",
			event:         "ProcessStopped",
			expectedState: "Error",
		},
		{
			name:          "Running to Stopping on ComponentsStopping",
			initialState:  "Running",
			event:         "ComponentsStopping",
			expectedState: "Stopping",
		},
		{
			name:          "Stopping to Stopped after ProcessStopped",
			initialState:  "Stopping",
			event:         "ProcessStopped",
			expectedState: "Stopped",
		},
		{
			name:          "Running to ErrorRecovery on ProcessError",
			initialState:  "Running",
			event:         "ProcessError",
			expectedState: "ErrorRecovery",
			processState:  NewProcessState(ProcessStateConfig{}, nil),
			checkProcess: func(t *testing.T, ps *ProcessState) {
				assert.Equal(t, "Stopped", ps.MustState().(string))
			},
		},
		{
			name:          "Starting to ErrorRecovery on ProcessError",
			initialState:  "Starting",
			event:         "ProcessError",
			expectedState: "Error", // Starting + ProcessError goes directly to Error, not ErrorRecovery
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Create test components for real coordination testing
			var components []ManagedComponent
			if tt.name != "Initializing to Starting" { // Simple state change doesn't need components
				// Add a test component that will actually start/ready/fail as needed
				testComponent := adapters.NewCmdComponent(adapters.CmdComponentConfig{
					Name:         "test-component",
					StartCommand: []string{"echo", "started"},
					ReadyCommand: []string{"echo", "ready"},
				})
				components = append(components, testComponent)
			}

			// Create system state
			config := SystemConfig{
				ProcessState: tt.processState,
				InitialState: tt.initialState,
				Components:   components,
			}
			ss := NewSystemState(config, nil)

			// Fire event
			require.NoError(t, ss.Fire(tt.event))

			// Check final state
			assert.Equal(t, tt.expectedState, ss.MustState().(string))

			// Check process state if needed
			if tt.checkProcess != nil {
				tt.checkProcess(t, tt.processState)
			}

			// Check component state if needed
			if tt.checkComponent != nil {
				tt.checkComponent(t, tt.componentState)
			}
		})
	}
}
