package main

import (
	"fmt"
	"io"
	"log"
	"os"
	"os/exec"
	"syscall"
	"time"
)

// ProcessManager handles the lifecycle of the supervised process
type ProcessManager struct {
	cmd          *exec.Cmd
	readyScript  string
	startCommand string
	env          *SpriteEnv
	readyChan    chan bool
	errorChan    chan error
	debug        bool
	name         string
}

// NewProcessManager creates a new process manager
func NewProcessManager(env *SpriteEnv, startCommand, readyScript string) *ProcessManager {
	return &ProcessManager{
		env:          env,
		startCommand: startCommand,
		readyScript:  readyScript,
		readyChan:    make(chan bool, 1),
		errorChan:    make(chan error, 1),
		debug:        env.debug,
		name:         "Process",
	}
}

// Start starts the supervised process
func (p *ProcessManager) Start() error {
	// Execute the script directly instead of using sh -c
	p.cmd = exec.Command(p.startCommand)

	if p.debug {
		log.Printf("DEBUG: Executing start command: %s", p.startCommand)
	}

	if p.readyScript == "" {
		// For processes without ready scripts, set up simple output forwarding
		stdout, err := p.cmd.StdoutPipe()
		if err != nil {
			return fmt.Errorf("failed to create stdout pipe: %v", err)
		}

		stderr, err := p.cmd.StderrPipe()
		if err != nil {
			return fmt.Errorf("failed to create stderr pipe: %v", err)
		}

		// Forward output directly to parent process
		go func() {
			io.Copy(os.Stdout, stdout)
		}()

		go func() {
			io.Copy(os.Stderr, stderr)
		}()
	} else {
		// For processes with ready scripts, set up pipes for monitoring
		stdout, err := p.cmd.StdoutPipe()
		if err != nil {
			return fmt.Errorf("failed to create stdout pipe: %v", err)
		}

		stderr, err := p.cmd.StderrPipe()
		if err != nil {
			return fmt.Errorf("failed to create stderr pipe: %v", err)
		}

		// Create a pipe to send output to both the ready script and parent process
		pr, pw := io.Pipe()

		// Forward stdout to both the pipe and parent process
		go func() {
			io.Copy(io.MultiWriter(pw, os.Stdout), stdout)
		}()

		// Forward stderr to parent process
		go func() {
			io.Copy(os.Stderr, stderr)
		}()

		// Start ready check in background
		go p.checkReady(pr)

		// Close pipe when process exits
		go func() {
			p.cmd.Wait()
			pw.Close()
		}()
	}

	// Start the process
	if err := p.cmd.Start(); err != nil {
		return fmt.Errorf("failed to start process: %v", err)
	}

	if p.debug {
		log.Printf("DEBUG: %s process started with PID: %d", p.name, p.cmd.Process.Pid)
	}

	// Update state
	p.env.state.ProcessState = ProcessStarting
	p.env.recordStateChange(p.env.state, p.env.state, "Process starting")

	// For processes without ready scripts, signal ready immediately
	if p.readyScript == "" {
		go func() {
			if p.debug {
				log.Printf("DEBUG: %s process ready (no ready script)", p.name)
			}
			p.readyChan <- true
		}()
	}

	// Start process monitoring
	go p.monitorProcess()

	return nil
}

// Stop stops the supervised process
func (p *ProcessManager) Stop() error {
	if p.cmd == nil || p.cmd.Process == nil {
		return nil
	}

	// Update state
	p.env.state.ProcessState = ProcessStopping
	p.env.recordStateChange(p.env.state, p.env.state, "Process stopping")

	// Send SIGTERM
	if err := p.cmd.Process.Signal(syscall.SIGTERM); err != nil {
		return fmt.Errorf("failed to send SIGTERM: %v", err)
	}

	// Wait for process to exit
	done := make(chan error, 1)
	go func() {
		done <- p.cmd.Wait()
	}()

	// Wait with timeout
	select {
	case err := <-done:
		if err != nil {
			return fmt.Errorf("process exited with error: %v", err)
		}
	case <-time.After(5 * time.Second):
		// Force kill after timeout
		if err := p.cmd.Process.Kill(); err != nil {
			return fmt.Errorf("failed to force kill process: %v", err)
		}
	}

	// Update state
	p.env.state.ProcessState = ProcessStopped
	p.env.recordStateChange(p.env.state, p.env.state, "Process stopped")

	return nil
}

// checkReady runs the ready script to determine when the process is ready
func (p *ProcessManager) checkReady(output io.Reader) {
	// This method is only called for processes WITH ready scripts
	if p.debug {
		log.Printf("DEBUG: Starting %s ready script: %s", p.name, p.readyScript)
	}

	// Execute the ready script directly instead of using sh -c
	cmd := exec.Command(p.readyScript)
	cmd.Stdin = output
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr

	// Run the ready script
	if err := cmd.Run(); err != nil {
		if p.debug {
			log.Printf("DEBUG: %s ready script failed: %v", p.name, err)
		}
		p.errorChan <- fmt.Errorf("ready script failed: %v", err)
		return
	}

	if p.debug {
		log.Printf("DEBUG: %s process is ready", p.name)
	}
	p.readyChan <- true
}

// monitorProcess monitors the process state and handles restarts
func (p *ProcessManager) monitorProcess() {
	for {
		select {
		case <-p.readyChan:
			p.env.state.ProcessState = ProcessRunning
			p.env.recordStateChange(p.env.state, p.env.state, "Process ready")

		case err := <-p.errorChan:
			if err != nil {
				p.env.state.ProcessState = ProcessCrashed
				p.env.state.ProcessExitCode = -1
			} else {
				p.env.state.ProcessState = ProcessExited
				p.env.state.ProcessExitCode = p.cmd.ProcessState.ExitCode()
			}
			p.env.recordStateChange(p.env.state, p.env.state, fmt.Sprintf("Process exited: %v", err))

			// Implement restart logic according to spec
			if !p.env.state.ShutdownInProgress {
				p.env.state.RestartAttempt++
				p.env.state.RestartDelay = p.env.nextRestartDelay()
				p.env.recordStateChange(p.env.state, p.env.state, "Scheduling restart")

				time.Sleep(time.Duration(p.env.state.RestartDelay) * time.Second)
				if err := p.Start(); err != nil {
					p.env.state.ProcessState = ProcessError
					p.env.recordStateChange(p.env.state, p.env.state, fmt.Sprintf("Failed to restart: %v", err))
				}
			}
		}
	}
}

// GetState returns the current state of the process
func (p *ProcessManager) GetState() string {
	return p.env.state.ProcessState
}
