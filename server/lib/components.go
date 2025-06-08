package lib

import (
	"fmt"
	"log"
	"os"
	"os/exec"
	"sync"
	"syscall"
	"time"
)

// ComponentState represents the possible states of a managed component
type ComponentState string

const (
	ComponentInitializing ComponentState = "Initializing"
	ComponentRunning      ComponentState = "Running"
	ComponentStopped      ComponentState = "Stopped"
	ComponentError        ComponentState = "Error"
)

// String implements the State interface
func (s ComponentState) String() string {
	return string(s)
}

// ComponentSetState represents the possible states of a component set
type ComponentSetState string

const (
	ComponentSetInitializing ComponentSetState = "Initializing"
	ComponentSetRunning      ComponentSetState = "Running"
	ComponentSetShuttingDown ComponentSetState = "ShuttingDown"
	ComponentSetShutdown     ComponentSetState = "Shutdown"
	ComponentSetStopped      ComponentSetState = "Stopped"
	ComponentSetError        ComponentSetState = "Error"
)

// String implements the State interface
func (s ComponentSetState) String() string {
	return string(s)
}

// Environment interface defines what ComponentManager and ProcessManager need from the environment
type Environment interface {
	UpdateComponentState(component string, newState string, oldState string)
	UpdateProcessState(newState string, oldState string)
}

// ComponentManager manages the lifecycle of a single component (DB or FS)
type ComponentManager struct {
	env             Environment
	name            string
	startCmd        string
	readyCmd        string
	debug           bool
	cmd             *exec.Cmd
	readyChan       chan bool
	stateManager    *StateManager
	stopInProgress  bool // Track if we're in the process of stopping
	stateChangeChan chan struct{}
}

// NewComponentManager creates a new component manager
func NewComponentManager(env Environment, debug bool, name, startCmd, readyCmd string) *ComponentManager {
	cm := &ComponentManager{
		env:       env,
		debug:     debug,
		name:      name,
		startCmd:  startCmd,
		readyCmd:  readyCmd,
		readyChan: make(chan bool, 1),
	}

	// Create and start StateManager
	cm.stateManager = NewStateManager(ComponentInitializing, debug)
	cm.stateManager.Start()

	// Register callback to notify environment of state changes
	cm.stateManager.OnTransition(func(oldState, newState State) {
		if cm.env != nil {
			cm.env.UpdateComponentState(cm.name, newState.String(), oldState.String())
		}
		// Signal readiness when transitioning to Running state
		if newState == ComponentRunning {
			if cm.debug {
				fmt.Printf("DEBUG: %s signaling readiness due to Running state\n", cm.name)
			}
			cm.SignalReady()
		}
	})

	return cm
}

// GetState returns the current state of the component
func (c *ComponentManager) GetState() string {
	return c.stateManager.GetState().String()
}

// setState updates the component's state
func (c *ComponentManager) setState(newState ComponentState) {
	c.stateManager.SetState(newState)
}

// Start starts the component
func (c *ComponentManager) Start() error {
	if c.debug {
		fmt.Printf("DEBUG: Starting component %s with command: %s\n", c.name, c.startCmd)
	}

	c.setState(ComponentInitializing)

	// Start the component process directly without sh
	c.cmd = exec.Command(c.startCmd)

	// Pass through stdout/stderr
	c.cmd.Stdout = os.Stdout
	c.cmd.Stderr = os.Stderr

	if err := c.cmd.Start(); err != nil {
		if c.debug {
			log.Printf("DEBUG: Failed to start %s: %v\nCommand: %s\nError: %+v", c.name, err, c.startCmd, err)
		}
		c.setState(ComponentError)
		return fmt.Errorf("failed to start %s: %v", c.name, err)
	}

	if c.debug {
		fmt.Printf("DEBUG: Component %s process started with PID %d\n", c.name, c.cmd.Process.Pid)
	}

	// Monitor the process
	go c.monitorProcess()

	// Check readiness in background
	go func() {
		for {
			select {
			default:
				if c.GetState() == ComponentInitializing.String() {
					// Check if component is ready
					if c.debug {
						fmt.Printf("DEBUG: Component %s running ready command: %s\n", c.name, c.readyCmd)
					}
					cmd := exec.Command(c.readyCmd)
					if err := cmd.Run(); err == nil {
						if c.debug {
							fmt.Printf("DEBUG: Component %s ready command succeeded\n", c.name)
						}
						c.setState(ComponentRunning)
						return
					} else if c.debug {
						fmt.Printf("DEBUG: Component %s ready command failed: %v\n", c.name, err)
					}
				}
				time.Sleep(500 * time.Millisecond)
			}
		}
	}()

	return nil
}

// Stop stops the component
func (c *ComponentManager) Stop() error {
	if c.GetState() == ComponentStopped.String() {
		return nil
	}

	// Create a channel to wait for state change
	stateChan := make(chan struct{})
	c.stateChangeChan = stateChan
	defer func() { c.stateChangeChan = nil }()

	// Send SIGTERM to the process
	if c.cmd.Process != nil {
		if err := c.cmd.Process.Signal(syscall.SIGTERM); err != nil {
			return fmt.Errorf("failed to send SIGTERM: %w", err)
		}
	}

	// Wait for state change or timeout
	select {
	case <-stateChan:
		return nil
	case <-time.After(30 * time.Second):
		// Force kill after timeout
		if c.cmd.Process != nil {
			if err := c.cmd.Process.Kill(); err != nil {
				return fmt.Errorf("failed to force kill process: %w", err)
			}
		}
		return nil
	}
}

// monitorProcess monitors the component's process and updates its state accordingly.
func (c *ComponentManager) monitorProcess() {
	err := c.cmd.Wait()
	if err != nil {
		if c.debug {
			log.Printf("DEBUG: Component %s process exited with error: %v", c.name, err)
		}
	}

	// Set state based on exit code
	if err == nil {
		c.setState(ComponentStopped)
	} else {
		c.setState(ComponentError)
	}

	// Signal state change if someone is waiting
	if c.stateChangeChan != nil {
		close(c.stateChangeChan)
	}
}

// ComponentSet represents a set of components that need to be managed together
type ComponentSet struct {
	components   map[string]*ComponentManager
	stateManager *StateManager
	debug        bool
	mu           sync.Mutex
	stopChan     chan bool
	done         chan struct{} // Signal when it's safe to stop sending state changes
}

// NewComponentSet creates a new ComponentSet
func NewComponentSet(debug bool) *ComponentSet {
	cs := &ComponentSet{
		components: make(map[string]*ComponentManager),
		stopChan:   make(chan bool, 1),
		done:       make(chan struct{}),
		debug:      debug,
	}

	// Create and start StateManager for aggregation
	cs.stateManager = NewStateManager(ComponentSetInitializing, debug)
	cs.stateManager.Start()

	// Set up aggregation function based on ComponentSet logic
	cs.stateManager.SetAggregationFunc(func(childStates []State) State {
		if len(childStates) == 0 {
			return ComponentSetInitializing
		}

		allRunning := true
		anyError := false
		anyStopped := false

		for _, state := range childStates {
			stateStr := state.String()
			if stateStr == ComponentError.String() {
				anyError = true
			} else if stateStr == ComponentStopped.String() {
				anyStopped = true
			} else if stateStr != ComponentRunning.String() {
				allRunning = false
			}
		}

		if anyError {
			return ComponentSetError
		} else if anyStopped {
			return ComponentSetStopped
		} else if allRunning {
			return ComponentSetRunning
		}
		return ComponentSetInitializing
	})

	return cs
}

// StateChanged returns the channel that receives state changes
func (cs *ComponentSet) StateChanged() <-chan State {
	return cs.stateManager.StateChanged()
}

// calculateOverallState determines the overall state of the component set
func (cs *ComponentSet) calculateOverallState() string {
	return cs.stateManager.GetState().String()
}

// setState sets the state of the component set
func (cs *ComponentSet) setState(newState ComponentSetState) {
	cs.stateManager.SetState(newState)
}

// AddComponent adds a component to the set
func (cs *ComponentSet) AddComponent(name string, component *ComponentManager) {
	cs.mu.Lock()
	defer cs.mu.Unlock()

	if cs.debug {
		fmt.Printf("DEBUG: Adding component %s to ComponentSet\n", name)
	}

	cs.components[name] = component

	// Add the component's StateManager as a child for automatic aggregation
	cs.stateManager.AddChild(component.stateManager)
}

// GetOverallState returns the overall state of the component set
func (cs *ComponentSet) GetOverallState() string {
	return cs.calculateOverallState()
}

// GetState returns a map of component names to their current states
func (cs *ComponentSet) GetState() map[string]string {
	states := make(map[string]string)
	for name, component := range cs.components {
		states[name] = component.GetState()
	}
	return states
}

// Start starts all components in the set
func (cs *ComponentSet) Start() error {
	cs.mu.Lock()
	defer cs.mu.Unlock()

	if cs.debug {
		fmt.Printf("DEBUG: Starting ComponentSet\n")
	}

	// Start all components
	for name, component := range cs.components {
		if cs.debug {
			fmt.Printf("DEBUG: Starting component %s\n", name)
		}
		if err := component.Start(); err != nil {
			if cs.debug {
				fmt.Printf("DEBUG: Error starting component %s: %v\n", name, err)
			}
			return err
		}
	}

	return nil
}

// TransitionToRunning transitions the ComponentSet to Running state when all components are ready
// Note: With StateManager aggregation, this happens automatically when all children become Running
func (cs *ComponentSet) TransitionToRunning() {
	if cs.debug {
		fmt.Printf("DEBUG: ComponentSet state will transition automatically via aggregation\n")
	}
	// State transition now happens automatically via StateManager aggregation
}

// Stop stops all components in the set
func (cs *ComponentSet) Stop() error {
	cs.mu.Lock()
	defer cs.mu.Unlock()

	currentState := cs.stateManager.GetState().String()
	if currentState == ComponentSetShutdown.String() {
		return nil
	}

	cs.setState(ComponentSetShuttingDown)

	// Signal that we're shutting down
	close(cs.done)

	// Stop all components
	for name, component := range cs.components {
		if err := component.Stop(); err != nil {
			cs.setState(ComponentSetError)
			return fmt.Errorf("failed to stop component %s: %w", name, err)
		}
	}

	cs.setState(ComponentSetShutdown)
	cs.stateManager.Close() // Properly close the StateManager
	close(cs.stopChan)
	return nil
}

// GetReadyChan returns the ready channel for the component
func (c *ComponentManager) GetReadyChan() <-chan bool {
	return c.readyChan
}

// SignalReady signals that the component is ready
func (c *ComponentManager) SignalReady() {
	select {
	case c.readyChan <- true:
	default:
	}
}

// StateChanged returns the channel for state changes
func (c *ComponentManager) StateChanged() <-chan State {
	return c.stateManager.StateChanged()
}

// GetComponents returns all components in the set
func (cs *ComponentSet) GetComponents() []*ComponentManager {
	cs.mu.Lock()
	defer cs.mu.Unlock()

	components := make([]*ComponentManager, 0, len(cs.components))
	for _, component := range cs.components {
		components = append(components, component)
	}
	return components
}

// GetStateManager returns the internal StateManager for integration with parent state managers
func (cs *ComponentSet) GetStateManager() *StateManager {
	return cs.stateManager
}
