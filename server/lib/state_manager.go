package lib

import (
	"fmt"
)

// State defines the interface that all state types must implement
type State interface {
	String() string
}

// StateManager manages state transitions and notifications.
type StateManager struct {
	currentState State
	stateChan    chan State
	internalChan chan State
	queryChan    chan chan State
	callbacks    []func(old, new State)
	debug        bool
	done         chan struct{}
	cleanup      chan struct{}
	running      bool

	// Child aggregation support
	children      []*StateManager
	aggregateFunc func([]State) State
}

// NewStateManager creates a new StateManager with the given initial state.
// Call Start() to begin processing state changes.
func NewStateManager(initialState State, debug bool) *StateManager {
	return &StateManager{
		currentState: initialState,
		stateChan:    make(chan State, 1),
		internalChan: make(chan State, 1),
		queryChan:    make(chan chan State),
		done:         make(chan struct{}),
		cleanup:      make(chan struct{}),
		debug:        debug,
		running:      false,
	}
}

// Start begins processing state changes. Must be called after setup.
func (sm *StateManager) Start() {
	if sm.running {
		return // Already started
	}
	sm.running = true
	go sm.run()
}

// run handles state transitions and notifications
func (sm *StateManager) run() {
	defer close(sm.cleanup)

	for {
		select {
		case newState := <-sm.internalChan:
			if newState != sm.currentState {
				oldState := sm.currentState
				sm.currentState = newState
				if sm.debug {
					fmt.Printf("DEBUG: State changing from %v to %v\n", oldState, newState)
				}
				// Send to external channel (non-blocking)
				select {
				case sm.stateChan <- newState:
				default:
					// Channel full, drop
				}
				// Call registered callbacks
				for _, cb := range sm.callbacks {
					cb(oldState, newState)
				}
			}
		case respChan := <-sm.queryChan:
			respChan <- sm.currentState
		case <-sm.done:
			close(sm.stateChan)
			return
		}
	}
}

// SetState transitions to the new state.
func (sm *StateManager) SetState(newState State) {
	if !sm.running {
		return // Not started yet
	}
	select {
	case sm.internalChan <- newState:
	case <-sm.done:
	}
}

// SetStateSync transitions to the new state and waits for it to be processed.
func (sm *StateManager) SetStateSync(newState State) {
	sm.SetState(newState)
	sm.Flush()
}

// Flush waits for all pending state changes to be processed.
func (sm *StateManager) Flush() {
	if !sm.running {
		return
	}
	// Send a query to force the goroutine to process all pending changes
	respChan := make(chan State, 1)
	select {
	case sm.queryChan <- respChan:
		<-respChan // Wait for response, which means all pending changes were processed
	case <-sm.done:
	}
}

// GetState returns the current state.
func (sm *StateManager) GetState() State {
	if !sm.running {
		return sm.currentState // Return stored state if not running
	}
	respChan := make(chan State, 1)
	select {
	case sm.queryChan <- respChan:
		return <-respChan
	case <-sm.done:
		return sm.currentState
	}
}

// StateChanged returns a read-only channel for state change notifications.
func (sm *StateManager) StateChanged() <-chan State {
	return sm.stateChan
}

// Close closes the state manager and its channels.
func (sm *StateManager) Close() {
	if !sm.running {
		return
	}
	close(sm.done)
	<-sm.cleanup
}

// OnTransition registers a callback function to be called on state transitions.
func (sm *StateManager) OnTransition(callback func(old, new State)) {
	sm.callbacks = append(sm.callbacks, callback)
}

// SetAggregationFunc sets the function used to compute this StateManager's state
// based on the states of its children. When children change state, this function
// will be called to recompute the parent state.
func (sm *StateManager) SetAggregationFunc(aggregateFunc func(childStates []State) State) {
	sm.aggregateFunc = aggregateFunc
}

// AddChild adds a child StateManager and starts listening to its state changes.
// When the child's state changes, the parent's aggregation function (if set) will
// be called to recompute the parent's state.
func (sm *StateManager) AddChild(child *StateManager) {
	sm.children = append(sm.children, child)

	// Set up callback to listen to child state changes
	child.OnTransition(func(old, new State) {
		if sm.debug {
			fmt.Printf("DEBUG: Child state changed from %v to %v, recomputing parent state\n", old, new)
		}
		// Use a goroutine to avoid deadlock when calling back into child.GetState()
		go sm.recomputeStateFromChildren()
	})

	// Recompute state immediately after adding child
	sm.recomputeStateFromChildren()
}

// RemoveChild removes a child StateManager and stops listening to its changes.
// Note: This doesn't remove the callback from the child (Go doesn't support that easily),
// but the parent will ignore updates after removal.
func (sm *StateManager) RemoveChild(childToRemove *StateManager) {
	for i, child := range sm.children {
		if child == childToRemove {
			// Remove from slice
			sm.children = append(sm.children[:i], sm.children[i+1:]...)
			break
		}
	}

	// Recompute state after removing child
	sm.recomputeStateFromChildren()
}

// recomputeStateFromChildren recalculates this StateManager's state based on
// all child states using the aggregation function.
func (sm *StateManager) recomputeStateFromChildren() {
	if sm.aggregateFunc == nil || len(sm.children) == 0 {
		return
	}

	// Collect all child states
	childStates := make([]State, len(sm.children))
	for i, child := range sm.children {
		childStates[i] = child.GetState()
	}

	// Compute new state using aggregation function
	newState := sm.aggregateFunc(childStates)

	if sm.debug {
		fmt.Printf("DEBUG: Aggregating %d child states into parent state: %v\n", len(childStates), newState)
	}

	// Set the new state
	sm.SetState(newState)
}

// GetChildren returns a copy of the child StateManagers slice.
func (sm *StateManager) GetChildren() []*StateManager {
	children := make([]*StateManager, len(sm.children))
	copy(children, sm.children)
	return children
}

// Global state enumeration
type GlobalState string

const (
	GlobalInitializing  GlobalState = "Initializing"
	GlobalRunning       GlobalState = "Running"
	GlobalCheckpointing GlobalState = "Checkpointing"
	GlobalRestoring     GlobalState = "Restoring"
	GlobalError         GlobalState = "Error"
	GlobalShuttingDown  GlobalState = "ShuttingDown"
	GlobalShutdown      GlobalState = "Shutdown"
)

func (gs GlobalState) String() string {
	return string(gs)
}

// Process state enumeration for StateManager (prefixed to avoid conflicts)
type SMProcessState string

const (
	SMProcessStopped   SMProcessState = "Stopped"
	SMProcessStarting  SMProcessState = "Starting"
	SMProcessRunning   SMProcessState = "Running"
	SMProcessStopping  SMProcessState = "Stopping"
	SMProcessSignaling SMProcessState = "Signaling"
	SMProcessCrashed   SMProcessState = "Crashed"
	SMProcessExited    SMProcessState = "Exited"
	SMProcessKilled    SMProcessState = "Killed"
	SMProcessError     SMProcessState = "Error"
)

func (ps SMProcessState) String() string {
	return string(ps)
}

// Boolean state for flags
type BooleanState string

const (
	BooleanTrue  BooleanState = "true"
	BooleanFalse BooleanState = "false"
)

func (bs BooleanState) String() string {
	return string(bs)
}

// Error type state
type ErrorTypeState string

const (
	ErrorTypeNone            ErrorTypeState = "None"
	ErrorTypeDBError         ErrorTypeState = "DBError"
	ErrorTypeFSError         ErrorTypeState = "FSError"
	ErrorTypeProcessError    ErrorTypeState = "ProcessError"
	ErrorTypeProcessCrash    ErrorTypeState = "ProcessCrash"
	ErrorTypeProcessKilled   ErrorTypeState = "ProcessKilled"
	ErrorTypeCheckpointError ErrorTypeState = "CheckpointError"
	ErrorTypeRestoreError    ErrorTypeState = "RestoreError"
	ErrorTypeStartupError    ErrorTypeState = "StartupError"
)

func (ets ErrorTypeState) String() string {
	return string(ets)
}
