package lib

import (
	"fmt"
	"log"
	"os/exec"
	"sync"
	"time"

	"sprites-env/lib/states"
)

// Environment interface defines what ComponentManager and ProcessManager need from the environment
type Environment interface {
	UpdateComponentState(component string, newState string, oldState string)
	UpdateProcessState(newState string, oldState string)
}

// ComponentManager manages the lifecycle of a single component (DB or FS)
type ComponentManager struct {
	env       Environment
	name      string
	startCmd  string
	readyCmd  string
	state     string
	mutex     sync.RWMutex
	debug     bool
	cmd       *exec.Cmd
	stopChan  chan bool
	readyChan chan bool
	errorChan chan error
}

// NewComponentManager creates a new component manager
func NewComponentManager(env Environment, debug bool, name, startCmd, readyCmd string) *ComponentManager {
	return &ComponentManager{
		env:       env,
		name:      name,
		startCmd:  startCmd,
		readyCmd:  readyCmd,
		state:     states.StateInitializing,
		debug:     debug,
		stopChan:  make(chan bool, 1),
		readyChan: make(chan bool, 1),
		errorChan: make(chan error, 1),
	}
}

// GetState returns the current state of the component
func (c *ComponentManager) GetState() string {
	c.mutex.RLock()
	defer c.mutex.RUnlock()
	return c.state
}

// setState updates the component state
func (c *ComponentManager) setState(newState string) {
	c.mutex.Lock()
	oldState := c.state
	c.state = newState
	c.mutex.Unlock()

	if c.env != nil {
		c.env.UpdateComponentState(c.name, newState, oldState)
	}

	if c.debug {
		fmt.Printf("DEBUG: %s state changed from %s to %s\n", c.name, oldState, newState)
	}
}

// Start starts the component
func (c *ComponentManager) Start() error {
	if c.debug {
		fmt.Printf("DEBUG: Starting component %s with command: %s\n", c.name, c.startCmd)
	}

	c.setState(states.StateInitializing)

	// Start the component process
	c.cmd = exec.Command("sh", "-c", c.startCmd)
	if err := c.cmd.Start(); err != nil {
		c.setState(states.StateError)
		return fmt.Errorf("failed to start %s: %v", c.name, err)
	}

	// Monitor the process
	go c.monitorProcess()

	// Check readiness
	go c.checkReady()

	return nil
}

// Stop stops the component
func (c *ComponentManager) Stop() error {
	if c.debug {
		fmt.Printf("DEBUG: Stopping component %s\n", c.name)
	}

	c.setState(states.StateShutdown)

	// Signal stop
	select {
	case c.stopChan <- true:
	default:
	}

	// Kill the process if it's running
	if c.cmd != nil && c.cmd.Process != nil {
		return c.cmd.Process.Kill()
	}

	return nil
}

// checkReady checks if the component is ready
func (c *ComponentManager) checkReady() {
	ticker := time.NewTicker(500 * time.Millisecond)
	defer ticker.Stop()

	for {
		select {
		case <-c.stopChan:
			return
		case <-ticker.C:
			if c.GetState() == states.StateInitializing {
				// Check if component is ready
				cmd := exec.Command("sh", "-c", c.readyCmd)
				if err := cmd.Run(); err == nil {
					c.setState(states.StateRunning)
					select {
					case c.readyChan <- true:
					default:
					}
					return
				}
			}
		}
	}
}

// monitorProcess monitors the component process
func (c *ComponentManager) monitorProcess() {
	if c.cmd == nil {
		return
	}

	if err := c.cmd.Wait(); err != nil {
		if c.debug {
			log.Printf("DEBUG: Component %s process exited with error: %v", c.name, err)
		}
		c.setState(states.StateError)
	}
}

// ComponentSet manages a set of components
type ComponentSet struct {
	components map[string]*ComponentManager
	mutex      sync.RWMutex
	debug      bool
}

// NewComponentSet creates a new component set
func NewComponentSet(debug bool) *ComponentSet {
	return &ComponentSet{
		components: make(map[string]*ComponentManager),
		debug:      debug,
	}
}

// AddComponent adds a component to the set
func (cs *ComponentSet) AddComponent(name string, component *ComponentManager) {
	cs.mutex.Lock()
	defer cs.mutex.Unlock()
	cs.components[name] = component
}

// Start starts all components in the set
func (cs *ComponentSet) Start() error {
	cs.mutex.RLock()
	defer cs.mutex.RUnlock()

	for name, component := range cs.components {
		if err := component.Start(); err != nil {
			return fmt.Errorf("failed to start component %s: %v", name, err)
		}
	}

	return nil
}

// Stop stops all components in the set
func (cs *ComponentSet) Stop() {
	cs.mutex.RLock()
	defer cs.mutex.RUnlock()

	for name, component := range cs.components {
		if cs.debug {
			fmt.Printf("DEBUG: Stopping component %s\n", name)
		}
		component.Stop()
	}
}

// GetState returns the state of all components
func (cs *ComponentSet) GetState() map[string]string {
	cs.mutex.RLock()
	defer cs.mutex.RUnlock()

	states := make(map[string]string)
	for name, component := range cs.components {
		states[name] = component.GetState()
	}

	return states
}

// GetOverallState returns the overall state of the component set
func (cs *ComponentSet) GetOverallState() string {
	states_map := cs.GetState()

	allRunning := true
	anyError := false

	for _, state := range states_map {
		if state == states.StateError {
			anyError = true
		}
		if state != states.StateRunning {
			allRunning = false
		}
	}

	if anyError {
		return states.StateError
	}
	if allRunning && len(states_map) > 0 {
		return states.StateRunning
	}

	return states.StateInitializing
}
