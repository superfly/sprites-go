package managers

import (
	"fmt"
	"testing"
	"time"

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
		{[]string{"SystemStarting"}, "Running", false, "", ""}, // Components and process start automatically
		// Test removed - can't fire ProcessRunning from Starting state (need to be in Ready state first)
		{[]string{"SystemStarting", "ComponentsStopping"}, "Stopped", false, "", ""}, // Stop during startup
		{[]string{"SystemStarting", "ProcessError"}, "Error", false, "", ""},         // Process error during startup
		{[]string{"SystemStarting", "ProcessCrashed"}, "Error", false, "", ""},       // Process crash during startup
		{[]string{"SystemStarting", "ComponentsError"}, "Error", false, "", ""},

		// Sequences starting from different initial states (testing InitialState functionality)
		{[]string{"ComponentsRunning"}, "Running", false, "", "Starting"}, // Components ready triggers process start
		{[]string{"ProcessRunning"}, "Running", false, "", "Ready"},       // Process starts from Ready state
		{[]string{"ComponentsStopping"}, "Stopped", false, "", "Running"},
		{[]string{"ProcessError"}, "Error", false, "", "Ready"}, // Process error leads to terminal Error state

		// Invalid sequences from default initial state
		{[]string{"ComponentsRunning"}, "Initializing", true, "ComponentsRunning", ""},                      // Can't have components run before starting
		{[]string{"ProcessRunning"}, "Initializing", true, "ProcessRunning", ""},                            // Can't run process from initial state
		{[]string{"SystemStarting", "Initializing"}, "Starting", true, "Initializing", ""},                  // Can't go back to Initializing
		{[]string{"SystemStarting", "ProcessError", "SystemStarting"}, "Error", true, "SystemStarting", ""}, // Can't restart from Error
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

			// Wait for state transitions to stabilize after firing all events
			if !sequence.ShouldFail {
				refs.WaitForStateStability(50*time.Millisecond, 500*time.Millisecond)
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
