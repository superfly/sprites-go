package managers

import (
	"context"
	"fmt"
	"os"
	"sprite-env/lib/adapters"
	"testing"
	"time"
)

// Helper function to create a system state manager that records all transitions
func createSystemWithRecording(t *testing.T) (*SystemState, *ProcessState, *[]string) {
	process := newTestManagedProcessWithSuccessfulStart()
	psm := NewProcessState(ProcessStateConfig{
		Process: process,
	}, []StateMonitor(nil))

	var stateChanges []string
	systemMonitor := newTestStateMonitor("SystemState", &stateChanges)

	ssm := NewSystemState(SystemConfig{
		ProcessState: psm,
	}, []StateMonitor{systemMonitor})

	return ssm, psm, &stateChanges
}

// testStateMonitor implements StateMonitor for testing
type testStateMonitor struct {
	name         string
	stateChanges *[]string
	events       chan StateTransition
}

func newTestStateMonitor(name string, stateChanges *[]string) *testStateMonitor {
	monitor := &testStateMonitor{
		name:         name,
		stateChanges: stateChanges,
		events:       make(chan StateTransition, 50), // Buffered channel
	}

	// Start a goroutine to process events
	go monitor.processEvents()

	return monitor
}

// Events implements StateMonitor interface
func (tsm *testStateMonitor) Events() chan<- StateTransition {
	return tsm.events
}

// processEvents processes state transition events for testing
func (tsm *testStateMonitor) processEvents() {
	for transition := range tsm.events {
		if transition.Name == tsm.name {
			*tsm.stateChanges = append(*tsm.stateChanges, transition.To)
		}
	}
}

func TestSystemStateManager_SystemTransitions(t *testing.T) {
	t.Run("Valid state sequences", func(t *testing.T) {
		validSequences := []struct {
			name        string
			description string
			sequence    func(*StateManagerRefs) error
		}{
			{
				name:        "Normal startup sequence",
				description: "System → Process → Components in correct order",
				sequence: func(refs *StateManagerRefs) error {
					if err := refs.System.Fire("SystemStarting"); err != nil {
						return err
					}
					if err := refs.System.Fire("SystemReady"); err != nil {
						return err
					}
					// Process is automatically started when system reaches Ready
					// So we just need to complete the process startup
					if err := refs.Process.Fire("Running"); err != nil {
						return err
					}
					return nil
				},
			},
			{
				name:        "Component startup coordination",
				description: "Components are automatically started when system starts",
				sequence: func(refs *StateManagerRefs) error {
					if err := refs.System.Fire("SystemStarting"); err != nil {
						return err
					}
					// Components should be automatically started by the system
					// We can verify they're in the right state
					time.Sleep(10 * time.Millisecond)
					if refs.ComponentGroup != nil {
						cgState := refs.ComponentGroup.MustState().(string)
						if cgState != "Starting" && cgState != "Running" {
							return fmt.Errorf("expected ComponentGroup to be Starting or Running, got %s", cgState)
						}
					}
					return nil
				},
			},
			{
				name:        "Stop during startup",
				description: "System can be stopped while in Starting state",
				sequence: func(refs *StateManagerRefs) error {
					if err := refs.System.Fire("SystemStarting"); err != nil {
						return err
					}
					if err := refs.System.Fire("ComponentsStopping"); err != nil {
						return err
					}
					if err := refs.System.Fire("ComponentsStopped"); err != nil {
						return err
					}
					return nil
				},
			},
		}

		for _, seq := range validSequences {
			t.Run(seq.name, func(t *testing.T) {
				refs, _ := createSystemWithAllManagers(t, 2)
				defer refs.System.Close()
				defer refs.Process.Close()

				err := seq.sequence(refs)
				if err != nil {
					t.Errorf("Valid sequence '%s' failed: %v", seq.description, err)
				}
			})
		}
	})

	t.Run("Invalid state sequences", func(t *testing.T) {
		invalidSequences := []struct {
			name        string
			description string
			sequence    func(*StateManagerRefs) error
			shouldFail  string // Which operation should fail
		}{
			{
				name:        "Skip system starting phase",
				description: "System cannot go directly from Initializing to Ready",
				shouldFail:  "System.Fire(SystemReady)",
				sequence: func(refs *StateManagerRefs) error {
					// Try to skip Starting phase
					return refs.System.Fire("SystemReady")
				},
			},
			{
				name:        "Backwards system transition",
				description: "System cannot go backwards from Starting to Initializing",
				shouldFail:  "System.Fire(Initializing)",
				sequence: func(refs *StateManagerRefs) error {
					if err := refs.System.Fire("SystemStarting"); err != nil {
						return err
					}
					// Try to go backwards
					return refs.System.Fire("Initializing")
				},
			},
			{
				name:        "Invalid trigger on process",
				description: "Process cannot receive invalid triggers",
				shouldFail:  "Process.Fire(InvalidTrigger)",
				sequence: func(refs *StateManagerRefs) error {
					// Try an invalid trigger
					return refs.Process.Fire("InvalidTrigger")
				},
			},
			{
				name:        "Terminal state escape",
				description: "Cannot escape terminal Error state",
				shouldFail:  "System.Fire(SystemStarting)",
				sequence: func(refs *StateManagerRefs) error {
					refs.System.Fire("SystemStarting")
					refs.System.Fire("SystemReady")
					refs.System.Fire("ProcessError")
					// Try to escape terminal state
					return refs.System.Fire("SystemStarting")
				},
			},
		}

		for _, seq := range invalidSequences {
			t.Run(seq.name, func(t *testing.T) {
				refs, _ := createSystemWithAllManagers(t, 2)
				defer refs.System.Close()
				defer refs.Process.Close()

				err := seq.sequence(refs)
				if err == nil {
					t.Errorf("Invalid sequence '%s' should have failed at %s", seq.description, seq.shouldFail)
				} else {
					t.Logf("Correctly rejected invalid sequence '%s': %v", seq.description, err)
				}
			})
		}
	})

	t.Run("Hierarchy constraint validation", func(t *testing.T) {
		// Test the key hierarchy constraints from TLA+ spec
		hierarchyTests := []struct {
			name        string
			setup       func(*StateManagerRefs) error
			constraint  func(*StateManagerRefs) bool
			description string
		}{
			{
				name: "System reaches Running when process runs",
				setup: func(refs *StateManagerRefs) error {
					if err := refs.System.Fire("SystemStarting"); err != nil {
						return err
					}

					// Manually transition components to Running (since mocks don't fire events)
					if refs.ComponentGroup != nil {
						// Check current state and only fire if needed
						cgState := refs.ComponentGroup.MustState().(string)
						if cgState == "Initializing" {
							if err := refs.ComponentGroup.Fire("Starting"); err != nil {
								return err
							}
						}

						// Now transition to Running
						cgState = refs.ComponentGroup.MustState().(string)
						if cgState == "Starting" {
							if err := refs.ComponentGroup.Fire("Running"); err != nil {
								return err
							}
						}
					}

					// Wait for system to react to component group becoming Running
					time.Sleep(10 * time.Millisecond)

					// Process should be automatically started when system reaches Ready
					// Check current state and only fire if needed
					processState := refs.Process.MustState().(string)
					if processState == "Initializing" {
						if err := refs.Process.Fire("Starting"); err != nil {
							return err
						}
					}

					// Complete the process startup to Running
					processState = refs.Process.MustState().(string)
					if processState == "Starting" {
						return refs.Process.Fire("Running")
					}

					return nil
				},
				constraint: func(refs *StateManagerRefs) bool {
					// When process is Running and system was Ready, system should be Running
					systemState := refs.System.MustState().(string)
					processState := refs.Process.MustState().(string)
					return processState == "Running" && systemState == "Running"
				},
				description: "SystemState=Running when ProcessState=Running and components ready",
			},
			{
				name: "Terminal states remain terminal",
				setup: func(refs *StateManagerRefs) error {
					// Use a simpler sequence that doesn't trigger automatic process startup
					if err := refs.System.Fire("SystemStarting"); err != nil {
						return err
					}
					// Fire ComponentsError to reach Error state without going through Ready
					// This avoids automatic process startup
					return refs.System.Fire("ComponentsError")
				},
				constraint: func(refs *StateManagerRefs) bool {
					// System should be in Error state and stay there
					systemState := refs.System.MustState().(string)
					return systemState == "Error"
				},
				description: "Terminal Error state is maintained",
			},
		}

		for _, test := range hierarchyTests {
			t.Run(test.name, func(t *testing.T) {
				refs, _ := createSystemWithAllManagers(t, 1)
				defer refs.System.Close()
				defer refs.Process.Close()

				if err := test.setup(refs); err != nil {
					t.Fatalf("Setup failed: %v", err)
				}

				time.Sleep(20 * time.Millisecond) // Allow async transitions

				if !test.constraint(refs) {
					systemState := refs.System.MustState().(string)
					processState := refs.Process.MustState().(string)
					var cgState string
					if refs.ComponentGroup != nil {
						cgState = refs.ComponentGroup.MustState().(string)
					}
					t.Errorf("Hierarchy constraint violated: %s. States: System=%s, Process=%s, ComponentGroup=%s",
						test.description, systemState, processState, cgState)
				}
			})
		}
	})
}

func TestSystemStateManager_InitialState(t *testing.T) {
	process := newTestManagedProcess()
	psm := NewProcessState(ProcessStateConfig{Process: process}, []StateMonitor(nil))
	defer psm.Close()

	ssm := NewSystemState(SystemConfig{
		ProcessState: psm,
	}, []StateMonitor(nil))

	initialState := ssm.MustState().(string)
	if initialState != "Initializing" {
		t.Errorf("Expected initial state to be Initializing, got %s", initialState)
	}
}

func TestSystemStateManager_TerminalStates(t *testing.T) {
	t.Run("Terminal states are truly terminal", func(t *testing.T) {
		refs, _ := createSystemWithAllManagers(t, 1)
		defer refs.System.Close()
		defer refs.Process.Close()

		// Test all terminal states
		terminalStates := []string{"Error", "Stopped"}

		for _, terminalState := range terminalStates {
			t.Run(terminalState+" is terminal", func(t *testing.T) {
				// Create a fresh system for each terminal state test
				testRefs, _ := createSystemWithAllManagers(t, 1)
				defer testRefs.System.Close()
				defer testRefs.Process.Close()

				// Get system to a state where we can reach the terminal state
				testRefs.System.Fire("SystemStarting")

				// Force system into terminal state
				switch terminalState {
				case "Error":
					testRefs.System.Fire("SystemReady")
					testRefs.System.Fire("ProcessError")
				case "Stopped":
					// For Stopped state, don't go to Ready (which starts process)
					// Instead go directly from Starting to Stopping to Stopped
					testRefs.System.Fire("ComponentsStopping")
					time.Sleep(5 * time.Millisecond)
					testRefs.System.Fire("ComponentsStopped")
				}

				time.Sleep(10 * time.Millisecond)

				// Verify we're in terminal state
				currentState := testRefs.System.MustState().(string)
				if currentState != terminalState {
					t.Errorf("Expected to reach terminal state %s, got %s", terminalState, currentState)
				}

				// Try all possible escape attempts - should all fail
				escapeAttempts := []string{
					"SystemStarting", "SystemReady", "ComponentsRunning",
					"ProcessRunning", "ComponentsStopping", "ProcessStopped",
				}

				for _, escape := range escapeAttempts {
					err := testRefs.System.Fire(escape)
					if err == nil {
						t.Errorf("Terminal state %s should not allow transition %s", terminalState, escape)
					}
				}
			})
		}
	})
}

func TestSystemStateManager_InvalidSequences(t *testing.T) {
	t.Run("Dynamic invalid sequence validation", func(t *testing.T) {
		refs, _ := createSystemWithAllManagers(t, 1)
		defer refs.System.Close()
		defer refs.Process.Close()

		// Test invalid transitions from each state
		stateTransitionTests := []struct {
			setupState    func(*StateManagerRefs) error
			invalidAction string
			description   string
		}{
			{
				setupState: func(refs *StateManagerRefs) error {
					// System starts in Initializing
					return nil
				},
				invalidAction: "SystemReady",
				description:   "Cannot skip Starting phase",
			},
			{
				setupState: func(refs *StateManagerRefs) error {
					return refs.System.Fire("SystemStarting")
				},
				invalidAction: "Initializing",
				description:   "Cannot go backwards to Initializing",
			},
			{
				setupState: func(refs *StateManagerRefs) error {
					refs.System.Fire("SystemStarting")
					return refs.System.Fire("SystemReady")
				},
				invalidAction: "SystemStarting",
				description:   "Cannot repeat SystemStarting from Ready",
			},
			{
				setupState: func(refs *StateManagerRefs) error {
					refs.System.Fire("SystemStarting")
					refs.System.Fire("SystemReady")
					return refs.System.Fire("ProcessError")
				},
				invalidAction: "SystemReady",
				description:   "Cannot escape terminal Error state",
			},
		}

		for _, test := range stateTransitionTests {
			t.Run(test.description, func(t *testing.T) {
				// Fresh system for each test
				testRefs, _ := createSystemWithAllManagers(t, 1)
				defer testRefs.System.Close()
				defer testRefs.Process.Close()

				// Setup the state
				if err := test.setupState(testRefs); err != nil {
					t.Fatalf("Setup failed: %v", err)
				}

				// Try the invalid action
				err := testRefs.System.Fire(test.invalidAction)
				if err == nil {
					currentState := testRefs.System.MustState().(string)
					t.Errorf("Invalid action '%s' should have failed from state '%s'", test.invalidAction, currentState)
				} else {
					t.Logf("Correctly rejected invalid action '%s': %v", test.invalidAction, err)
				}
			})
		}
	})

	t.Run("Cross-manager constraint violations", func(t *testing.T) {
		refs, _ := createSystemWithAllManagers(t, 1)
		defer refs.System.Close()
		defer refs.Process.Close()

		// Test violations of hierarchy constraints between managers
		constraintTests := []struct {
			name        string
			setup       func() error
			violation   func() error
			description string
		}{
			{
				name: "Process cannot start before system ready",
				setup: func() error {
					// System in Starting (not Ready)
					return refs.System.Fire("SystemStarting")
				},
				violation: func() error {
					return refs.Process.Fire("Starting")
				},
				description: "Process.Fire(Starting) when SystemState != Ready",
			},
			{
				name: "Process cannot run before system ready",
				setup: func() error {
					// System in Initializing
					return nil
				},
				violation: func() error {
					return refs.Process.Fire("Running")
				},
				description: "Process.Fire(Running) when SystemState = Initializing",
			},
		}

		for _, test := range constraintTests {
			t.Run(test.name, func(t *testing.T) {
				// Fresh system for each test
				testRefs, _ := createSystemWithAllManagers(t, 1)
				defer testRefs.System.Close()
				defer testRefs.Process.Close()

				// Setup the state
				if err := test.setup(); err != nil {
					t.Fatalf("Setup failed: %v", err)
				}

				// Try the constraint violation
				err := test.violation()
				if err == nil {
					systemState := testRefs.System.MustState().(string)
					processState := testRefs.Process.MustState().(string)
					t.Errorf("Constraint violation should have failed: %s. States: System=%s, Process=%s",
						test.description, systemState, processState)
				} else {
					t.Logf("Correctly rejected constraint violation '%s': %v", test.description, err)
				}
			})
		}
	})
}

func TestSystemStateManager_ComponentIntegration(t *testing.T) {
	t.Run("Process starts when system reaches Ready", func(t *testing.T) {
		// Create process that tracks start calls
		process := newTestManagedProcessWithSuccessfulStart()
		psm := NewProcessState(ProcessStateConfig{Process: process}, []StateMonitor(nil))
		defer psm.Close()

		// Create system without components for simple control
		ssm := NewSystemState(SystemConfig{
			ProcessState: psm,
		}, []StateMonitor(nil))

		// System starts in Initializing
		if ssm.MustState().(string) != "Initializing" {
			t.Errorf("Expected system state 'Initializing', got '%s'", ssm.MustState().(string))
		}

		// Process should NOT have been started yet
		if process.getStartCalls() > 0 {
			t.Errorf("Process should not be started until system reaches Ready, but got %d start calls", process.getStartCalls())
		}

		// Transition to Starting
		ssm.Fire("SystemStarting")
		if ssm.MustState().(string) != "Starting" {
			t.Errorf("Expected system state 'Starting', got '%s'", ssm.MustState().(string))
		}

		// Process should STILL not be started
		if process.getStartCalls() > 0 {
			t.Errorf("Process should not be started in Starting state, but got %d start calls", process.getStartCalls())
		}

		// Transition to Ready - NOW process should start
		ssm.Fire("SystemReady")
		if ssm.MustState().(string) != "Ready" {
			t.Errorf("Expected system state 'Ready', got '%s'", ssm.MustState().(string))
		}

		// Brief wait for OnEntry callback to execute
		time.Sleep(5 * time.Millisecond)

		// Process should have been started exactly once
		if process.getStartCalls() != 1 {
			t.Errorf("Process should be started exactly once when system reaches Ready, got %d start calls", process.getStartCalls())
		}
	})

	t.Run("ErrorRecovery state triggers process stop", func(t *testing.T) {
		// Create system with nil process for control
		psm := NewProcessState(ProcessStateConfig{Process: nil}, []StateMonitor(nil))
		defer psm.Close()

		ssm := NewSystemState(SystemConfig{
			ProcessState: psm,
		}, []StateMonitor(nil))

		// Get to Ready state
		ssm.Fire("SystemStarting")
		ssm.Fire("SystemReady")

		// Manually put process in Running state
		psm.Fire("Starting")
		psm.Fire("Running")

		if psm.MustState().(string) != "Running" {
			t.Errorf("Expected process to be Running, got '%s'", psm.MustState().(string))
		}

		// Now fire ComponentsErrorStopping to enter ErrorRecovery
		ssm.Fire("ComponentsErrorStopping")

		// System should be in ErrorRecovery
		if ssm.MustState().(string) != "ErrorRecovery" {
			t.Errorf("Expected system state 'ErrorRecovery', got '%s'", ssm.MustState().(string))
		}

		// Brief wait for OnEntry callback to execute
		time.Sleep(5 * time.Millisecond)

		// Process should now be in Stopping state (ErrorRecovery OnEntry should have triggered it)
		if psm.MustState().(string) != "Stopping" {
			t.Errorf("Expected process to be Stopping after ErrorRecovery, got '%s'", psm.MustState().(string))
		}
	})

	t.Run("StateMonitor records all manager transitions", func(t *testing.T) {
		// Test that StateMonitor properly records state changes
		var systemStates []string
		var processStates []string

		systemMonitor := newTestStateMonitor("SystemState", &systemStates)
		processMonitor := newTestStateMonitor("ProcessState", &processStates)

		process := newTestManagedProcessWithSuccessfulStart()
		psm := NewProcessState(ProcessStateConfig{Process: process}, []StateMonitor{processMonitor})
		defer psm.Close()

		ssm := NewSystemState(SystemConfig{
			ProcessState: psm,
		}, []StateMonitor{systemMonitor})

		// Execute some transitions
		ssm.Fire("SystemStarting")
		ssm.Fire("SystemReady")
		psm.Fire("Starting")
		psm.Fire("Running")

		time.Sleep(20 * time.Millisecond)

		// Verify system state changes were recorded
		expectedSystemStates := []string{"Starting", "Ready"}
		if len(systemStates) != len(expectedSystemStates) {
			t.Errorf("Expected %v system state changes, got %v", expectedSystemStates, systemStates)
		}

		// Verify process state changes were recorded
		expectedProcessStates := []string{"Starting", "Running"}
		if len(processStates) != len(expectedProcessStates) {
			t.Errorf("Expected %v process state changes, got %v", expectedProcessStates, processStates)
		}
	})
}

func TestSystemState_OperationalScenarios(t *testing.T) {
	t.Run("Scenario 1: Stop during component startup", func(t *testing.T) {
		// Create system with 2 components and get all manager references
		refs, stateChanges := createSystemWithAllManagers(t, 2)
		defer refs.System.Close()
		defer refs.Process.Close()

		// Start the system
		err := refs.System.Fire("SystemStarting")
		if err != nil {
			t.Fatalf("Failed to fire SystemStarting: %v", err)
		}

		// Give time for components to start
		time.Sleep(50 * time.Millisecond)

		// System should be in Starting state
		currentState := refs.System.MustState().(string)
		if currentState != "Starting" {
			t.Errorf("Expected Starting state, got %s", currentState)
		}

		// Trigger stop on component group (simulating stop during startup)
		err = refs.ComponentGroup.Fire("Stopping")
		if err != nil {
			t.Fatalf("Failed to fire Stopping on ComponentGroup: %v", err)
		}

		// Give time for async operations
		time.Sleep(50 * time.Millisecond)

		// Fire ComponentsStopped to complete the transition
		err = refs.ComponentGroup.Fire("Stopped")
		if err != nil {
			t.Fatalf("Failed to fire Stopped on ComponentGroup: %v", err)
		}

		// Give time for system to react
		time.Sleep(50 * time.Millisecond)

		// Should eventually reach Stopped
		currentState = refs.System.MustState().(string)
		if currentState != "Stopped" {
			t.Errorf("Expected final state to be Stopped, got %s", currentState)
		}

		// Verify state progression: Starting → Stopping → Stopped
		if len(*stateChanges) < 3 {
			t.Errorf("Expected at least 3 state changes, got %d: %v", len(*stateChanges), *stateChanges)
		}

		if (*stateChanges)[0] != "Starting" {
			t.Errorf("Expected first state to be Starting, got %s", (*stateChanges)[0])
		}

		if (*stateChanges)[1] != "Stopping" {
			t.Errorf("Expected second state to be Stopping, got %s", (*stateChanges)[1])
		}

		if (*stateChanges)[2] != "Stopped" {
			t.Errorf("Expected third state to be Stopped, got %s", (*stateChanges)[2])
		}
	})

	t.Run("Scenario 2: Component failure during startup", func(t *testing.T) {
		// Create system with 2 components and get all manager references
		refs, stateChanges := createSystemWithAllManagers(t, 2)
		defer refs.System.Close()
		defer refs.Process.Close()

		// Start the system
		err := refs.System.Fire("SystemStarting")
		if err != nil {
			t.Fatalf("Failed to fire SystemStarting: %v", err)
		}

		// Give time for components to start
		time.Sleep(50 * time.Millisecond)

		// System should be in Starting state initially
		currentState := refs.System.MustState().(string)
		if currentState != "Starting" {
			t.Errorf("Expected Starting state, got %s", currentState)
		}

		// Simulate component failure during startup by triggering Error on first component
		if len(refs.Components) > 0 {
			err = refs.Components[0].Fire("Error")
			if err != nil {
				t.Fatalf("Failed to fire Error on first component: %v", err)
			}
		}

		// Give time for component group to react to component failure
		time.Sleep(50 * time.Millisecond)

		// Component group should be in ErrorStopping state
		if refs.ComponentGroup != nil {
			cgState := refs.ComponentGroup.MustState().(string)
			if cgState != "ErrorStopping" {
				t.Errorf("Expected ComponentGroup to be in ErrorStopping, got %s", cgState)
			}
		}

		// System should now be in ErrorRecovery
		currentState = refs.System.MustState().(string)
		if currentState != "ErrorRecovery" {
			t.Errorf("Expected ErrorRecovery state, got %s", currentState)
		}

		// Process should be in Stopping state (triggered by ErrorRecovery)
		time.Sleep(50 * time.Millisecond)
		processState := refs.Process.MustState().(string)
		if processState != "Stopping" {
			t.Errorf("Expected Process to be in Stopping, got %s", processState)
		}

		// Complete process stop
		err = refs.Process.Fire("Stopped")
		if err != nil {
			t.Fatalf("Failed to fire Stopped on Process: %v", err)
		}

		// Complete component group error recovery
		err = refs.ComponentGroup.Fire("Error")
		if err != nil {
			t.Fatalf("Failed to fire Error on ComponentGroup: %v", err)
		}

		// Give time for system to react
		time.Sleep(50 * time.Millisecond)

		// System should reach final Error state
		currentState = refs.System.MustState().(string)
		if currentState != "Error" {
			t.Errorf("Expected final state to be Error, got %s", currentState)
		}

		// Verify state progression: Starting → ErrorRecovery → Error
		if len(*stateChanges) < 3 {
			t.Errorf("Expected at least 3 state changes, got %d: %v", len(*stateChanges), *stateChanges)
		}

		if (*stateChanges)[0] != "Starting" {
			t.Errorf("Expected first state to be Starting, got %s", (*stateChanges)[0])
		}

		if (*stateChanges)[1] != "ErrorRecovery" {
			t.Errorf("Expected second state to be ErrorRecovery, got %s", (*stateChanges)[1])
		}

		if (*stateChanges)[2] != "Error" {
			t.Errorf("Expected third state to be Error, got %s", (*stateChanges)[2])
		}
	})

	t.Run("Scenario 3: Direct transitions on different managers", func(t *testing.T) {
		// Create system with 1 component and get all manager references
		refs, stateChanges := createSystemWithAllManagers(t, 1)
		defer refs.System.Close()
		defer refs.Process.Close()

		// Test triggering transitions on different managers

		// 1. Start system via System manager
		err := refs.System.Fire("SystemStarting")
		if err != nil {
			t.Fatalf("Failed to fire SystemStarting on System: %v", err)
		}

		// 2. Start components via ComponentGroup manager
		err = refs.ComponentGroup.Fire("Starting")
		if err != nil {
			t.Fatalf("Failed to fire Starting on ComponentGroup: %v", err)
		}

		// 3. Make component ready via individual Component manager
		if len(refs.Components) > 0 {
			err = refs.Components[0].Fire("Running")
			if err != nil {
				t.Fatalf("Failed to fire Running on Component: %v", err)
			}
		}

		// Give time for state propagation
		time.Sleep(100 * time.Millisecond)

		// 4. Start process via Process manager
		err = refs.Process.Fire("Starting")
		if err != nil {
			t.Fatalf("Failed to fire Starting on Process: %v", err)
		}

		err = refs.Process.Fire("Running")
		if err != nil {
			t.Fatalf("Failed to fire Running on Process: %v", err)
		}

		// Give time for final state propagation
		time.Sleep(100 * time.Millisecond)

		// System should reach Running state
		currentState := refs.System.MustState().(string)
		if currentState != "Running" {
			t.Errorf("Expected final state to be Running, got %s", currentState)
		}

		// Verify we have recorded multiple state changes
		if len(*stateChanges) < 3 {
			t.Errorf("Expected at least 3 state changes, got %d: %v", len(*stateChanges), *stateChanges)
		}

		t.Logf("State progression: %v", *stateChanges)
	})
}

// mockManagedComponent is a test component that doesn't fire events automatically
type mockManagedComponent struct {
	name string
}

func newTestManagedComponentWithoutEvents() ManagedComponent {
	return &mockManagedComponent{name: "test"}
}

func (m *mockManagedComponent) GetName() string {
	return m.name
}

func (m *mockManagedComponent) Start(ctx context.Context) error {
	// Do nothing - no automatic events
	return nil
}

func (m *mockManagedComponent) Stop() {
	// Do nothing - no automatic events
}

func (m *mockManagedComponent) Checkpoint() error {
	// Do nothing - no automatic events
	return nil
}

func (m *mockManagedComponent) Restore() error {
	// Do nothing - no automatic events
	return nil
}

func (m *mockManagedComponent) Events() <-chan adapters.ComponentEventType {
	// Return a channel that never sends events
	return make(<-chan adapters.ComponentEventType)
}

// mockManagedProcess is a test process that doesn't fire events automatically
type mockManagedProcess struct {
	name string
}

func newTestManagedProcessWithoutEvents() ManagedProcess {
	return &mockManagedProcess{name: "test"}
}

func (m *mockManagedProcess) Start(ctx context.Context) error {
	// Do nothing - no automatic events
	return nil
}

func (m *mockManagedProcess) Stop() {
	// Do nothing - no automatic events
}

func (m *mockManagedProcess) Signal(sig os.Signal) {
	// Do nothing - no automatic events
}

func (m *mockManagedProcess) Events() <-chan adapters.ProcessEventType {
	// Return a channel that never sends events
	return make(<-chan adapters.ProcessEventType)
}

// StateManagerRefs holds references to all state managers for testing
type StateManagerRefs struct {
	System         *SystemState
	Process        *ProcessState
	ComponentGroup *ComponentGroupState
	Components     []*ComponentState
}

// createSystemWithAllManagers creates a system with all state managers exposed for testing
func createSystemWithAllManagers(t *testing.T, numComponents int) (*StateManagerRefs, *[]string) {
	// Create mock components that don't fire events automatically
	var components []ManagedComponent
	for i := 0; i < numComponents; i++ {
		components = append(components, newTestManagedComponentWithoutEvents())
	}

	// Create mock process that doesn't fire events automatically
	process := newTestManagedProcessWithoutEvents()
	psm := NewProcessState(ProcessStateConfig{
		Process: process,
	}, []StateMonitor(nil))

	// Create state change recorder
	var stateChanges []string
	systemMonitor := newTestStateMonitor("SystemState", &stateChanges)

	// Create system config
	config := SystemConfig{
		ProcessState: psm,
		Components:   components,
	}

	// Create system state manager
	ssm := NewSystemState(config, []StateMonitor{systemMonitor})

	// Get references to all state managers
	refs := &StateManagerRefs{
		System:  ssm,
		Process: psm,
	}

	// Get component group reference (if components exist)
	if len(components) > 0 {
		refs.ComponentGroup = ssm.componentGroupState

		// Get individual component references
		if refs.ComponentGroup != nil {
			refs.Components = refs.ComponentGroup.GetComponentStates()
		}
	}

	return refs, &stateChanges
}
