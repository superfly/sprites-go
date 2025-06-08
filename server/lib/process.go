package lib

import (
	"fmt"
	"log"
	"os/exec"
	"syscall"
	"time"
)

// ProcessState represents the possible states of a managed process
type ProcessState string

const (
	ProcessInitializing ProcessState = "Initializing"
	ProcessStarting     ProcessState = "Starting"
	ProcessRunning      ProcessState = "Running"
	ProcessStopping     ProcessState = "Stopping"
	ProcessStopped      ProcessState = "Stopped"
	ProcessCrashed      ProcessState = "Crashed"
	ProcessKilled       ProcessState = "Killed"
	ProcessError        ProcessState = "Error"
)

// String implements the State interface
func (s ProcessState) String() string {
	return string(s)
}

// ProcessManager manages a supervised process
type ProcessManager struct {
	env          Environment
	debug        bool
	command      string
	args         []string
	cmd          *exec.Cmd
	stateManager *StateManager
	done         chan struct{}
	stopChan     chan struct{}
	started      bool
}

// NewProcessManager creates a new process manager
func NewProcessManager(env Environment, debug bool, command string, args ...string) *ProcessManager {
	pm := &ProcessManager{
		env:      env,
		debug:    debug,
		command:  command,
		args:     args,
		done:     make(chan struct{}),
		stopChan: make(chan struct{}),
		started:  true, // Mark as started since we start StateManager immediately
	}

	// Create and start StateManager immediately
	pm.stateManager = NewStateManager(ProcessInitializing, debug)
	pm.stateManager.Start()

	// Register callback to notify environment of state changes
	pm.stateManager.OnTransition(func(oldState, newState State) {
		if pm.env != nil {
			pm.env.UpdateProcessState(newState.String(), oldState.String())
		}
	})

	return pm
}

// GetState returns the current state of the process
func (p *ProcessManager) GetState() ProcessState {
	return p.stateManager.GetState().(ProcessState)
}

// setState sets the state of the process
func (pm *ProcessManager) setState(newState ProcessState) {
	pm.stateManager.SetState(newState)
}

// logDebug logs a debug message with process information
func (p *ProcessManager) logDebug(format string, args ...interface{}) {
	if !p.debug {
		return
	}
	cmdStr := ""
	if p.cmd != nil {
		cmdStr = fmt.Sprintf(" [%s %v]", p.cmd.Path, p.cmd.Args)
	} else if p.command != "" {
		cmdStr = fmt.Sprintf(" [%s %v]", p.command, p.args)
	}
	log.Printf("DEBUG: Process%s: "+format, append([]interface{}{cmdStr}, args...)...)
}

// Start starts the supervised process
func (pm *ProcessManager) Start() error {
	if pm.debug {
		fmt.Printf("DEBUG: Starting supervised process: %s %v\n", pm.command, pm.args)
	}

	// Set up command
	cmd := exec.Command(pm.command, pm.args...)
	pm.cmd = cmd

	// Set up output forwarding
	if pm.debug {
		fmt.Printf("DEBUG: Setting up output forwarding for process\n")
	}

	// Update state to Starting
	pm.setState(ProcessStarting)

	// Start process
	if err := cmd.Start(); err != nil {
		if pm.debug {
			fmt.Printf("DEBUG: Failed to start process: %v\n", err)
		}
		// Set error state and wait for it to be processed before returning
		pm.stateManager.SetStateSync(ProcessError)
		return err
	}

	if pm.debug {
		fmt.Printf("DEBUG: Process started successfully, PID: %d\n", cmd.Process.Pid)
	}

	// Update state to Running
	pm.setState(ProcessRunning)

	// Start monitoring the process in the background
	go pm.monitorProcess()

	return nil
}

// Stop stops the supervised process
func (pm *ProcessManager) Stop() error {
	if pm.debug {
		fmt.Printf("DEBUG: Stopping supervised process\n")
	}

	if pm.cmd != nil && pm.cmd.Process != nil {
		// Check if process is already finished
		if pm.cmd.ProcessState != nil {
			if pm.debug {
				fmt.Printf("DEBUG: Process already finished, no need to stop\n")
			}
			return nil
		}

		pm.setState(ProcessStopping)
		if err := pm.cmd.Process.Signal(syscall.SIGTERM); err != nil {
			if pm.debug {
				fmt.Printf("DEBUG: Error sending SIGTERM: %v\n", err)
			}
			return err
		}

		// Wait for the monitor goroutine to signal completion
		// The monitor will handle the Wait() and state transitions
		select {
		case <-pm.done:
			// Process exited normally
		case <-time.After(5 * time.Second):
			// Timeout - force kill
			if pm.debug {
				fmt.Printf("DEBUG: Process didn't exit within 5 seconds, force killing\n")
			}
			pm.ForceKill()
			pm.setState(ProcessKilled)
		}
	}

	return nil
}

// monitorProcess monitors the supervised process
func (p *ProcessManager) monitorProcess() {
	if p.cmd == nil {
		close(p.done)
		return
	}

	if err := p.cmd.Wait(); err != nil {
		log.Printf("ERROR: Supervised process exited with error: %v", err)

		// Check if it was killed
		if exitError, ok := err.(*exec.ExitError); ok {
			if exitError.ExitCode() == -1 || exitError.ExitCode() == 137 { // Killed
				p.setState(ProcessKilled)
			} else {
				p.setState(ProcessCrashed)
			}
		} else {
			p.setState(ProcessError)
		}
	} else {
		p.logDebug("Supervised process exited successfully")
		p.setState(ProcessStopped)
	}

	// Signal that we're done monitoring
	close(p.done)
}

// GetExitCode returns the exit code of the process
func (p *ProcessManager) GetExitCode() int {
	if p.cmd == nil || p.cmd.ProcessState == nil {
		return -1
	}
	return p.cmd.ProcessState.ExitCode()
}

// ForceKill force-kills the supervised process
func (p *ProcessManager) ForceKill() {
	if p.cmd != nil && p.cmd.Process != nil {
		if p.debug {
			fmt.Printf("DEBUG: Force-killing supervised process\n")
		}
		p.cmd.Process.Kill()
	}
}

// Exited returns a channel that will be closed when the process has exited
func (p *ProcessManager) Exited() <-chan struct{} {
	return p.done
}
