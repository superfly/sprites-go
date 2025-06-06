package lib

import (
	"context"
	"fmt"
	"log"
	"os"
	"os/exec"
	"sync"
	"syscall"
	"time"

	"sprite-env/server/lib/states"
)

// ProcessManager manages the lifecycle of a supervised process
type ProcessManager struct {
	env       Environment
	command   string
	args      string
	state     string
	process   *exec.Cmd
	debug     bool
	mutex     sync.RWMutex
	stopChan  chan bool
	exitCode  int
	exitError error
	ctx       context.Context
	cancel    context.CancelFunc
}

// NewProcessManager creates a new process manager
func NewProcessManager(env Environment, debug bool, command, args string) *ProcessManager {
	ctx, cancel := context.WithCancel(context.Background())

	return &ProcessManager{
		env:      env,
		command:  command,
		args:     args,
		state:    states.ProcessStateStopped,
		debug:    debug,
		stopChan: make(chan bool, 1),
		exitCode: 0,
		ctx:      ctx,
		cancel:   cancel,
	}
}

// GetState returns the current state of the process
func (p *ProcessManager) GetState() string {
	p.mutex.RLock()
	defer p.mutex.RUnlock()
	return p.state
}

// setState updates the process state and notifies the environment
func (p *ProcessManager) setState(newState string) {
	p.mutex.Lock()
	oldState := p.state
	p.state = newState
	p.mutex.Unlock()

	// Notify environment of state change
	if p.env != nil {
		p.env.UpdateProcessState(newState, oldState)
	}

	if p.debug {
		log.Printf("DEBUG: Process state changed from %s to %s", oldState, newState)
	}
}

// Start starts the supervised process
func (p *ProcessManager) Start() error {
	if p.debug {
		fmt.Printf("DEBUG: Starting supervised process: %s\n", p.command)
	}

	p.setState(states.ProcessStateStarting)

	// Start the process
	if p.args != "" {
		p.process = exec.Command("sh", "-c", p.command+" "+p.args)
	} else {
		p.process = exec.Command("sh", "-c", p.command)
	}

	// Set up output forwarding
	p.process.Stdout = os.Stdout
	p.process.Stderr = os.Stderr

	if err := p.process.Start(); err != nil {
		p.setState(states.ProcessStateError)
		return fmt.Errorf("failed to start process: %v", err)
	}

	p.setState(states.ProcessStateRunning)

	// Monitor the process
	go p.monitorProcess()

	return nil
}

// Stop stops the supervised process and waits for it to actually stop
func (p *ProcessManager) Stop() error {
	if p.debug {
		fmt.Printf("DEBUG: Stopping supervised process\n")
	}

	p.setState(states.ProcessStateStopping)

	// Signal stop
	select {
	case p.stopChan <- true:
	default:
	}

	// Send SIGTERM to the process
	if p.process != nil && p.process.Process != nil {
		if err := p.process.Process.Signal(syscall.SIGTERM); err != nil {
			if p.debug {
				log.Printf("DEBUG: Failed to send SIGTERM: %v", err)
			}
		}

		// Wait a bit for graceful shutdown
		gracefulTimeout := time.NewTimer(5 * time.Second)
		defer gracefulTimeout.Stop()

		// Create a channel to signal when process stops
		done := make(chan bool, 1)
		go func() {
			for {
				state := p.GetState()
				if state == states.ProcessStateKilled || state == states.ProcessStateExited || state == states.ProcessStateCrashed || state == states.ProcessStateError {
					done <- true
					return
				}
				time.Sleep(100 * time.Millisecond)
			}
		}()

		select {
		case <-done:
			// Process stopped gracefully
			return nil
		case <-gracefulTimeout.C:
			// Force kill if still running
			if p.debug {
				log.Printf("DEBUG: Graceful shutdown timeout, force killing process")
			}
			p.setState(states.ProcessStateSignaling)
			if err := p.process.Process.Kill(); err != nil {
				if p.debug {
					log.Printf("DEBUG: Failed to kill process: %v", err)
				}
			}

			// Wait for force kill to complete (with timeout)
			forceTimeout := time.NewTimer(2 * time.Second)
			defer forceTimeout.Stop()

			select {
			case <-done:
				// Process finally stopped
				return nil
			case <-forceTimeout.C:
				// Something is very wrong, but don't hang forever
				if p.debug {
					log.Printf("DEBUG: Force kill timeout exceeded, giving up")
				}
				p.setState(states.ProcessStateError)
				return fmt.Errorf("process failed to stop within timeout")
			}
		}
	}

	return nil
}

// monitorProcess monitors the supervised process
func (p *ProcessManager) monitorProcess() {
	if p.process == nil {
		return
	}

	if err := p.process.Wait(); err != nil {
		if p.debug {
			log.Printf("DEBUG: Supervised process exited with error: %v", err)
		}

		// Check if it was killed
		if exitError, ok := err.(*exec.ExitError); ok {
			p.exitCode = exitError.ExitCode()
			if p.exitCode == -1 || p.exitCode == 137 { // Killed
				p.setState(states.ProcessStateKilled)
			} else {
				p.setState(states.ProcessStateCrashed)
			}
		} else {
			p.setState(states.ProcessStateError)
		}
	} else {
		if p.debug {
			log.Printf("DEBUG: Supervised process exited successfully")
		}
		p.exitCode = 0
		p.setState(states.ProcessStateExited)
	}
}

// GetExitCode returns the exit code of the process
func (p *ProcessManager) GetExitCode() int {
	p.mutex.RLock()
	defer p.mutex.RUnlock()
	return p.exitCode
}

// ForceKill force-kills the supervised process
func (p *ProcessManager) ForceKill() {
	if p.process != nil && p.process.Process != nil {
		if p.debug {
			fmt.Printf("DEBUG: Force-killing supervised process\n")
		}
		p.process.Process.Kill()
	}
}

// isStoppedState checks if the given state represents a stopped process
func (p *ProcessManager) isStoppedState(state string) bool {
	return state == states.ProcessStateKilled || state == states.ProcessStateExited || state == states.ProcessStateCrashed || state == states.ProcessStateError
}
