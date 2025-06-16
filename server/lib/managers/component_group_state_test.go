package managers

import (
	"testing"
	"time"
)

func TestComponentGroupState_NormalStartup(t *testing.T) {
	// Create test components that will succeed
	comp1 := newTestManagedComponentWithSuccessfulOperations()
	comp2 := newTestManagedComponentWithSuccessfulOperations()
	comp3 := newTestManagedComponentWithSuccessfulOperations()

	config := ComponentGroupConfig{
		Components: []ManagedComponent{comp1, comp2, comp3},
	}

	cgsm := NewComponentGroupState(config, nil)
	defer cgsm.Close()

	// Initial state should be Initializing
	if state := cgsm.MustState().(string); state != "Initializing" {
		t.Errorf("Expected initial state 'Initializing', got '%s'", state)
	}

	// Trigger Starting - should start all components
	err := cgsm.Fire("Starting")
	if err != nil {
		t.Errorf("Failed to fire Starting: %v", err)
	}

	// Wait for components to start and reach Running
	time.Sleep(100 * time.Millisecond)

	// Group should now be Running
	if state := cgsm.MustState().(string); state != "Running" {
		t.Errorf("Expected group state 'Running', got '%s'", state)
	}

	// All component managers should be Running
	for i, csm := range cgsm.componentManagers {
		if state := csm.MustState().(string); state != "Running" {
			t.Errorf("Expected component %d state 'Running', got '%s'", i+1, state)
		}
	}
}

func TestComponentGroupState_ComponentError(t *testing.T) {
	// Create test components - one will fail on start
	comp1 := newTestManagedComponentWithSuccessfulOperations() // Success
	comp2 := newTestManagedComponent()                         // Fail on start
	comp3 := newTestManagedComponentWithSuccessfulOperations() // Success

	config := ComponentGroupConfig{
		Components: []ManagedComponent{comp1, comp2, comp3},
	}

	// Record state transitions
	var stateChanges []string
	monitor := &testStateMonitor{
		name:         "ComponentGroupStateManager",
		stateChanges: &stateChanges,
		events:       make(chan StateTransition, 50),
	}
	go monitor.processEvents()

	cgsm := NewComponentGroupState(config, monitor)
	defer cgsm.Close()

	// Trigger Starting
	err := cgsm.Fire("Starting")
	if err != nil {
		t.Errorf("Failed to fire Starting: %v", err)
	}

	// Wait for all transitions to complete
	time.Sleep(200 * time.Millisecond)

	// Verify that ErrorStopping was reached during the sequence
	errorStoppingReached := false
	for _, state := range stateChanges {
		if state == "ErrorStopping" {
			errorStoppingReached = true
			break
		}
	}

	if !errorStoppingReached {
		t.Errorf("Expected ErrorStopping state to be reached during error recovery. State sequence: %v", stateChanges)
	}

	// Final state should be Error
	finalState := cgsm.MustState().(string)
	if finalState != "Error" {
		t.Errorf("Expected final state 'Error', got '%s'", finalState)
	}

	// Failed component (index 1) should be in Error state
	if state := cgsm.componentManagers[1].MustState().(string); state != "Error" {
		t.Errorf("Expected failed component state 'Error', got '%s'", state)
	}
}

func TestComponentGroupState_Stop(t *testing.T) {
	// Create test components that will succeed
	comp1 := newTestManagedComponentWithSuccessfulOperations()
	comp2 := newTestManagedComponentWithSuccessfulOperations()

	config := ComponentGroupConfig{
		Components: []ManagedComponent{comp1, comp2},
	}

	cgsm := NewComponentGroupState(config, nil)
	defer cgsm.Close()

	// Start up components
	cgsm.Fire("Starting")
	time.Sleep(100 * time.Millisecond)

	// Should be Running
	if state := cgsm.MustState().(string); state != "Running" {
		t.Errorf("Expected group state 'Running', got '%s'", state)
	}

	// Trigger stop
	err := cgsm.Fire("Stopping")
	if err != nil {
		t.Errorf("Failed to fire Stopping: %v", err)
	}

	// Wait for stop processing
	time.Sleep(100 * time.Millisecond)

	// Group should be in Stopped state
	if state := cgsm.MustState().(string); state != "Stopped" {
		t.Errorf("Expected group state 'Stopped', got '%s'", state)
	}
}
