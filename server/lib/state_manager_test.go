package lib

import (
	"fmt"
	"testing"
	"time"
)

// TestStateType is a custom type for testing generic state management
type TestStateType string

const (
	TestStateA TestStateType = "A"
	TestStateB TestStateType = "B"
	TestStateC TestStateType = "C"
)

// String implements the State interface
func (t TestStateType) String() string {
	return string(t)
}

// StringState is a string-based state type for testing
type StringState string

// String implements the State interface
func (s StringState) String() string {
	return string(s)
}

// IntState is an int-based state type for testing
type IntState int

// String implements the State interface
func (i IntState) String() string {
	return fmt.Sprintf("%d", i)
}

// CustomState is a struct-based state type for testing
type CustomState struct {
	Value int
	Label string
}

// String implements the State interface
func (c CustomState) String() string {
	return fmt.Sprintf("%s-%d", c.Label, c.Value)
}

// TestStateManagerBasicOperations tests basic state management operations
func TestStateManagerBasicOperations(t *testing.T) {
	sm := NewStateManager(TestStateA, true)
	defer sm.Close()

	// Test initial state (before starting)
	if got := sm.GetState(); got != TestStateA {
		t.Errorf("Initial state = %v, want %v", got, TestStateA)
	}

	// Start processing
	sm.Start()

	// Test state transition
	sm.SetState(TestStateB)
	time.Sleep(10 * time.Millisecond) // Allow state to propagate

	if got := sm.GetState(); got != TestStateB {
		t.Errorf("State after transition = %v, want %v", got, TestStateB)
	}

	// Test no-op state change
	sm.SetState(TestStateB)
	time.Sleep(10 * time.Millisecond)

	if got := sm.GetState(); got != TestStateB {
		t.Errorf("State after no-op change = %v, want %v", got, TestStateB)
	}
}

// TestStateManagerCallbacks tests callback functionality
func TestStateManagerCallbacks(t *testing.T) {
	sm := NewStateManager(TestStateA, true)
	defer sm.Close()

	transitions := make([]struct{ old, new TestStateType }, 0)
	mu := make(chan struct{}, 1) // Simple mutex using channel

	// Register callback during setup phase
	sm.OnTransition(func(old, new State) {
		mu <- struct{}{}
		transitions = append(transitions, struct{ old, new TestStateType }{old.(TestStateType), new.(TestStateType)})
		<-mu
	})

	// Start processing
	sm.Start()

	// Test state transitions
	sm.SetState(TestStateB)
	sm.SetState(TestStateC)
	sm.SetState(TestStateC) // Should not trigger callback

	// Wait for callbacks to complete
	time.Sleep(50 * time.Millisecond)

	// Verify transitions
	expected := []struct{ old, new TestStateType }{
		{TestStateA, TestStateB},
		{TestStateB, TestStateC},
	}

	mu <- struct{}{}
	if len(transitions) != len(expected) {
		t.Errorf("Got %d transitions, want %d", len(transitions), len(expected))
		<-mu
		return
	}

	for i, exp := range expected {
		if transitions[i].old != exp.old || transitions[i].new != exp.new {
			t.Errorf("Transition %d = (%v, %v), want (%v, %v)",
				i, transitions[i].old, transitions[i].new, exp.old, exp.new)
		}
	}
	<-mu
}

// TestStateManagerChannelBehavior tests channel behavior
func TestStateManagerChannelBehavior(t *testing.T) {
	sm := NewStateManager(TestStateA, true)

	// Set up channel listener during setup phase
	stateChan := sm.StateChanged()

	// Start processing
	sm.Start()

	// Test state change notification
	sm.SetState(TestStateB)
	select {
	case state := <-stateChan:
		if state != TestStateB {
			t.Errorf("State = %v, want %v", state, TestStateB)
		}
	case <-time.After(100 * time.Millisecond):
		t.Error("Timeout waiting for state change")
	}

	// Verify channel is closed after Close()
	sm.Close()
	select {
	case _, ok := <-stateChan:
		if ok {
			t.Error("Channel should be closed")
		}
	case <-time.After(100 * time.Millisecond):
		t.Error("Timeout waiting for channel close")
	}
}

/*
// TestStateManagerTypeSafety tests type safety with different state types
func TestStateManagerTypeSafety(t *testing.T) {
	// Test with string-based state type
	stringSM := NewStateManager[StringState](StringState("initial"), true)
	defer stringSM.Close()
	stringSM.Start()
	stringSM.SetState(StringState("new"))

	// Test with int-based state type
	intSM := NewStateManager[IntState](IntState(0), true)
	defer intSM.Close()
	intSM.Start()
	intSM.SetState(IntState(1))

	// Test with custom state type
	customSM := NewStateManager[CustomState](CustomState{0, "initial"}, true)
	defer customSM.Close()
	customSM.Start()
	customSM.SetState(CustomState{1, "new"})
}

// TestStateManagerMultipleCallbacks tests multiple callback registration
func TestStateManagerMultipleCallbacks(t *testing.T) {
	sm := NewStateManager[TestStateType](TestStateA, true)
	defer sm.Close()

	callback1Count := 0
	callback2Count := 0

	// Register multiple callbacks during setup phase
	sm.OnTransition(func(old, new TestStateType) {
		callback1Count++
	})
	sm.OnTransition(func(old, new TestStateType) {
		callback2Count++
	})

	// Start processing
	sm.Start()

	// Trigger state changes
	sm.SetState(TestStateB)
	sm.SetState(TestStateC)

	// Wait for callbacks to complete
	time.Sleep(50 * time.Millisecond)

	// Verify both callbacks were called the correct number of times
	if callback1Count != 2 {
		t.Errorf("Callback1 called %d times, want 2", callback1Count)
	}
	if callback2Count != 2 {
		t.Errorf("Callback2 called %d times, want 2", callback2Count)
	}
}

func TestStateManagerAggregation(t *testing.T) {
	// Test basic aggregation functionality
	parent := NewStateManager(StringState("Initializing"), true)
	child1 := NewStateManager(StringState("Initializing"), true)
	child2 := NewStateManager(StringState("Initializing"), true)

	// Set up aggregation function - all children must be "Running" for parent to be "Running"
	parent.SetAggregationFunc(func(childStates []StringState) StringState {
		allRunning := true
		anyError := false
		for _, state := range childStates {
			if state == StringState("Error") {
				anyError = true
			}
			if state != StringState("Running") {
				allRunning = false
			}
		}
		if anyError {
			return StringState("Error")
		}
		if allRunning {
			return StringState("Running")
		}
		return StringState("Initializing")
	})

	// Start all state managers
	parent.Start()
	child1.Start()
	child2.Start()

	// Add children
	parent.AddChild(child1)
	parent.AddChild(child2)

	// Initially all should be "Initializing"
	if parent.GetState() != "Initializing" {
		t.Errorf("Expected parent state to be 'Initializing', got '%s'", parent.GetState())
	}

	// Transition first child to Running
	child1.SetState("Running")
	time.Sleep(50 * time.Millisecond)

	// Parent should still be Initializing (not all children running)
	if parent.GetState() != "Initializing" {
		t.Errorf("Expected parent state to be 'Initializing', got '%s'", parent.GetState())
	}

	// Transition second child to Running
	child2.SetState("Running")
	time.Sleep(50 * time.Millisecond)

	// Now parent should be Running
	if parent.GetState() != "Running" {
		t.Errorf("Expected parent state to be 'Running', got '%s'", parent.GetState())
	}

	// Transition one child to Error
	child1.SetState("Error")
	time.Sleep(50 * time.Millisecond)

	// Parent should be Error
	if parent.GetState() != "Error" {
		t.Errorf("Expected parent state to be 'Error', got '%s'", parent.GetState())
	}

	// Clean up
	parent.Close()
	child1.Close()
	child2.Close()
}

func TestStateManagerChildRemoval(t *testing.T) {
	parent := NewStateManager("Initializing", true)
	child1 := NewStateManager("Initializing", true)
	child2 := NewStateManager("Initializing", true)

	// Simple aggregation: Running if any child is Running
	parent.SetAggregationFunc(func(childStates []string) string {
		for _, state := range childStates {
			if state == "Running" {
				return "Running"
			}
		}
		return "Initializing"
	})

	parent.Start()
	child1.Start()
	child2.Start()

	// Add both children
	parent.AddChild(child1)
	parent.AddChild(child2)

	// Set one child to Running
	child1.SetState("Running")
	time.Sleep(50 * time.Millisecond)

	if parent.GetState() != "Running" {
		t.Errorf("Expected parent state to be 'Running', got '%s'", parent.GetState())
	}

	// Remove the running child
	parent.RemoveChild(child1)
	time.Sleep(50 * time.Millisecond)

	// Parent should be back to Initializing (only child2 which is Initializing)
	if parent.GetState() != "Initializing" {
		t.Errorf("Expected parent state to be 'Initializing' after child removal, got '%s'", parent.GetState())
	}

	// Verify child count
	children := parent.GetChildren()
	if len(children) != 1 {
		t.Errorf("Expected 1 child after removal, got %d", len(children))
	}

	// Changes to removed child should not affect parent
	child1.SetState("Error")
	time.Sleep(50 * time.Millisecond)

	if parent.GetState() != "Initializing" {
		t.Errorf("Expected parent state to remain 'Initializing' after removed child changes, got '%s'", parent.GetState())
	}

	// Clean up
	parent.Close()
	child1.Close()
	child2.Close()
}

func TestStateManagerNoAggregationFunc(t *testing.T) {
	// Test that adding children without aggregation function doesn't crash
	parent := NewStateManager("Initializing", true)
	child := NewStateManager("Running", true)

	parent.Start()
	child.Start()

	initialState := parent.GetState()
	parent.AddChild(child)
	time.Sleep(50 * time.Millisecond)

	// Parent state should be unchanged
	if parent.GetState() != initialState {
		t.Errorf("Expected parent state to remain '%s', got '%s'", initialState, parent.GetState())
	}

	// Clean up
	parent.Close()
	child.Close()
}
*/

func TestComponentManagerStateManager(t *testing.T) {
	// Test ComponentManager with StateManager integration
	cm := NewComponentManager(nil, true, "test-component", "echo hello", "true")
	defer cm.stateManager.Close()

	// Test initial state
	if cm.GetState() != ComponentInitializing.String() {
		t.Errorf("Expected initial state to be '%s', got '%s'", ComponentInitializing.String(), cm.GetState())
	}

	// Test state transition
	cm.setState(ComponentRunning)
	time.Sleep(10 * time.Millisecond)

	if cm.GetState() != ComponentRunning.String() {
		t.Errorf("Expected state to be '%s', got '%s'", ComponentRunning.String(), cm.GetState())
	}
}

func TestComponentSetAggregation(t *testing.T) {
	// Test ComponentSet with StateManager aggregation
	cs := NewComponentSet(true)
	defer cs.stateManager.Close()

	// Create two components
	cm1 := NewComponentManager(nil, true, "component1", "echo hello", "true")
	cm2 := NewComponentManager(nil, true, "component2", "echo world", "true")
	defer cm1.stateManager.Close()
	defer cm2.stateManager.Close()

	// Add components to set
	cs.AddComponent("component1", cm1)
	cs.AddComponent("component2", cm2)

	// Initially should be Initializing
	time.Sleep(50 * time.Millisecond)
	if cs.GetOverallState() != ComponentSetInitializing.String() {
		t.Errorf("Expected ComponentSet state to be '%s', got '%s'", ComponentSetInitializing.String(), cs.GetOverallState())
	}

	// Transition first component to Running
	cm1.setState(ComponentRunning)
	time.Sleep(50 * time.Millisecond)

	// Should still be Initializing (not all components running)
	if cs.GetOverallState() != ComponentSetInitializing.String() {
		t.Errorf("Expected ComponentSet state to be '%s', got '%s'", ComponentSetInitializing.String(), cs.GetOverallState())
	}

	// Transition second component to Running
	cm2.setState(ComponentRunning)
	time.Sleep(50 * time.Millisecond)

	// Now should be Running
	if cs.GetOverallState() != ComponentSetRunning.String() {
		t.Errorf("Expected ComponentSet state to be '%s', got '%s'", ComponentSetRunning.String(), cs.GetOverallState())
	}

	// Transition one component to Error
	cm1.setState(ComponentError)
	time.Sleep(50 * time.Millisecond)

	// Should be Error
	if cs.GetOverallState() != ComponentSetError.String() {
		t.Errorf("Expected ComponentSet state to be '%s', got '%s'", ComponentSetError.String(), cs.GetOverallState())
	}
}
