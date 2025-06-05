package main

import (
	"fmt"
	"io"
	"log"
	"os"
	"os/exec"
	"sync/atomic"
)

// Component states
const (
	StateReady = "Ready"
)

// ComponentManager handles the lifecycle of a state component (DB or FS)
type ComponentManager struct {
	name         string
	startCommand string
	readyCommand string
	env          *SpriteEnv
	supervisor   *Supervisor
	state        atomic.Value // Use atomic.Value for lock-free state updates
	readyChan    chan struct{}
	errorChan    chan error
	debug        bool
}

// ComponentSet manages all storage components as a cohesive unit
type ComponentSet struct {
	components map[string]*ComponentManager
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
	cs.components[name] = component
}

// Start starts all components concurrently
func (cs *ComponentSet) Start() error {
	if cs.debug {
		log.Printf("DEBUG: ComponentSet: Starting %d components", len(cs.components))
	}

	for name, component := range cs.components {
		go func(n string, c *ComponentManager) {
			if err := c.Start(); err != nil {
				log.Printf("Failed to start component %s: %v", n, err)
				os.Exit(1)
			}
		}(name, component)
	}

	return nil
}

// Stop stops all components
func (cs *ComponentSet) Stop() error {
	if cs.debug {
		log.Printf("DEBUG: ComponentSet: Stopping %d components", len(cs.components))
	}

	for name, component := range cs.components {
		if cs.debug {
			log.Printf("DEBUG: ComponentSet: Stopping component %s", name)
		}
		component.Stop()
	}

	return nil
}

// GetState returns the overall state of the component set
func (cs *ComponentSet) GetState() map[string]string {
	states := make(map[string]string)
	for name, component := range cs.components {
		states[name] = component.GetState()
	}
	return states
}

// GetOverallState returns a single state representing the set
func (cs *ComponentSet) GetOverallState() string {
	states := cs.GetState()

	// If any component is in error, set is in error
	for _, state := range states {
		if state == StateError {
			return StateError
		}
	}

	// If any component is initializing, set is initializing
	for _, state := range states {
		if state == StateInitializing {
			return StateInitializing
		}
	}

	// If any component is shutting down, set is shutting down
	for _, state := range states {
		if state == StateShutdown {
			return StateShutdown
		}
	}

	// If all components are running, set is running
	allRunning := true
	for _, state := range states {
		if state != StateRunning {
			allRunning = false
			break
		}
	}
	if allRunning {
		return StateRunning
	}

	// Default to initializing
	return StateInitializing
}

// NewComponentManager creates a new component manager
func NewComponentManager(env *SpriteEnv, name, startCommand, readyScript string) *ComponentManager {
	cm := &ComponentManager{
		name:         name,
		env:          env,
		startCommand: startCommand,
		readyCommand: readyScript,
		supervisor:   NewSupervisor(env.debug),
		readyChan:    make(chan struct{}),
		errorChan:    make(chan error, 1),
		debug:        env.debug,
	}
	cm.state.Store(StateInitializing)
	return cm
}

// GetState returns the current state of the component
func (c *ComponentManager) GetState() string {
	return c.state.Load().(string)
}

// setState updates the component state according to TLA+ spec
func (c *ComponentManager) setState(newState string) {
	if c.debug {
		log.Printf("DEBUG: %s: State transition: %s -> %s", c.name, c.GetState(), newState)
	}
	c.state.Store(newState)
}

// Start starts the component
func (c *ComponentManager) Start() error {
	if c.debug {
		log.Printf("DEBUG: %s: Starting component", c.name)
	}

	// Start the process using supervisor
	if err := c.supervisor.Start(c.startCommand); err != nil {
		return fmt.Errorf("failed to start component: %v", err)
	}

	if c.debug {
		log.Printf("DEBUG: %s: Start command completed", c.name)
	}

	// According to TLA+ spec, state is already Initializing
	// Start ready check in background
	go c.checkReady(nil)

	// Start process monitoring
	go c.monitorProcess()

	if c.debug {
		log.Printf("DEBUG: %s: Start sequence completed", c.name)
	}
	return nil
}

// Stop stops the component
func (c *ComponentManager) Stop() error {
	c.state.Store(StateShutdown)

	// Stop the process using supervisor
	if err := c.supervisor.Stop(); err != nil {
		return fmt.Errorf("failed to stop component: %v", err)
	}

	return nil
}

// checkReady runs the ready script to check if the component is ready
func (c *ComponentManager) checkReady(output io.Reader) {
	if c.debug {
		log.Printf("DEBUG: %s: Starting ready check", c.name)
	}

	// Execute the ready script directly instead of using sh -c
	cmd := exec.Command(c.readyCommand)
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr

	if c.debug {
		log.Printf("DEBUG: %s: Executing ready command: %s", c.name, c.readyCommand)
	}

	// Run the ready script
	if err := cmd.Run(); err != nil {
		if c.debug {
			log.Printf("DEBUG: %s: Ready check failed: %v", c.name, err)
		}
		// Signal error state
		select {
		case c.errorChan <- err:
		default:
			if c.debug {
				log.Printf("DEBUG: %s: Error channel full, dropping error", c.name)
			}
		}
		return
	}

	if c.debug {
		log.Printf("DEBUG: %s: Ready command completed successfully", c.name)
	}

	// According to TLA+ spec, transition from Initializing to Running
	c.setState(StateRunning)

	// Signal ready state
	if c.debug {
		log.Printf("DEBUG: %s: Signaling ready state", c.name)
	}
	select {
	case c.readyChan <- struct{}{}:
		if c.debug {
			log.Printf("DEBUG: %s: Ready signal sent", c.name)
		}
	default:
		if c.debug {
			log.Printf("DEBUG: %s: Ready channel blocked, state already updated", c.name)
		}
	}

	if c.debug {
		log.Printf("DEBUG: %s: Ready check completed successfully", c.name)
	}
}

// monitorProcess monitors the component state
func (c *ComponentManager) monitorProcess() {
	for {
		select {
		case <-c.readyChan:
			if c.debug {
				log.Printf("DEBUG: %s: Received ready signal", c.name)
			}
			// State is already updated in checkReady

		case err := <-c.errorChan:
			if c.debug {
				log.Printf("DEBUG: %s: Received error signal: %v", c.name, err)
			}
			// According to TLA+ spec, transition to Error state
			c.setState(StateError)

			// According to spec, any component failure is critical - exit immediately
			if c.debug {
				log.Printf("DEBUG: %s: Component failure, exiting system", c.name)
			}
			os.Exit(1)
		}
	}
}
