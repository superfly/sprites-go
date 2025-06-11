package lib

import (
	"bufio"
	"context"
	"fmt"
	"io"
	"os/exec"
	"sync"
)

// ComponentEventType defines the type of event that can be emitted by a component.
type ComponentEventType string

const (
	// ComponentStarting is emitted when the component is about to be started.
	ComponentStarting ComponentEventType = "starting"
	// ComponentStarted is emitted when the start process has successfully started.
	ComponentStarted ComponentEventType = "started"
	// ComponentChecking is emitted when the ready check is being performed.
	ComponentChecking ComponentEventType = "checking"
	// ComponentReady is emitted when the component is ready (ready script succeeded or no ready script).
	ComponentReady ComponentEventType = "ready"
	// ComponentStopping is emitted when a stop sequence has been initiated.
	ComponentStopping ComponentEventType = "stopping"
	// ComponentStopped is emitted when the component has stopped.
	ComponentStopped ComponentEventType = "stopped"
	// ComponentFailed is emitted when the component has failed permanently.
	ComponentFailed ComponentEventType = "failed"
)

// ComponentConfig holds configuration for a component
type ComponentConfig struct {
	StartCommand      []string // Start script, REQUIRED
	ReadyCommand      []string // Ready check script, nil if not available
	CheckpointCommand []string // Checkpoint script, nil if not available
	RestoreCommand    []string // Restore script, nil if not available
}

// Component manages the lifecycle of a component using the process supervisor
type Component struct {
	config ComponentConfig

	startProcess *Process

	events chan ComponentEventType
}

// NewComponent creates a new component manager
func NewComponent(config ComponentConfig) *Component {
	return &Component{
		config: config,
		events: make(chan ComponentEventType),
	}
}

// Events returns the event channel for this component
func (c *Component) Events() <-chan ComponentEventType {
	return c.events
}

// Start initiates the component startup process
func (c *Component) Start(ctx context.Context) error {
	if len(c.config.StartCommand) == 0 {
		return fmt.Errorf("no start command configured")
	}

	// Start the supervision process
	go c.supervise(ctx)

	return nil
}

// Stop stops the component
func (c *Component) Stop() {
	if c.startProcess != nil {
		c.startProcess.Stop()
	}
}

// Checkpoint performs a checkpoint operation on the component
func (c *Component) Checkpoint(ctx context.Context) error {
	if len(c.config.CheckpointCommand) == 0 {
		return nil // No checkpoint command configured
	}

	checkpointProcess := NewProcess(ProcessConfig{
		Command:    c.config.CheckpointCommand,
		MaxRetries: 0, // No retries for checkpoint
	})

	events := checkpointProcess.Start(ctx)

	// Wait for checkpoint to complete
	for event := range events {
		switch event {
		case EventFailed:
			return fmt.Errorf("checkpoint failed")
		case EventStopped:
			return nil // Success
		}
	}

	return nil
}

// Restore performs a restore operation on the component
func (c *Component) Restore(ctx context.Context) error {
	if len(c.config.RestoreCommand) == 0 {
		return nil // No restore command configured
	}

	restoreProcess := NewProcess(ProcessConfig{
		Command:    c.config.RestoreCommand,
		MaxRetries: 0, // No retries for restore
	})

	events := restoreProcess.Start(ctx)

	// Wait for restore to complete
	for event := range events {
		switch event {
		case EventFailed:
			return fmt.Errorf("restore failed")
		case EventStopped:
			return nil // Success
		}
	}

	return nil
}

// supervise handles the component lifecycle
func (c *Component) supervise(ctx context.Context) {
	defer close(c.events)

	c.events <- ComponentStarting

	// Create the main process
	c.startProcess = NewProcess(ProcessConfig{
		Command:    c.config.StartCommand,
		MaxRetries: 0, // No auto-restart for components
	})

	var startEvents <-chan EventType
	var startStdout, startStderr io.ReadCloser
	var err error

	// If we have a ready command, we need to capture the output for piping
	if len(c.config.ReadyCommand) > 0 {
		startStdout, err = c.startProcess.StdoutPipe()
		if err != nil {
			c.events <- ComponentFailed
			return
		}
		startStderr, err = c.startProcess.StderrPipe()
		if err != nil {
			c.events <- ComponentFailed
			return
		}
	}

	// Start the process and monitor events
	startEvents = c.startProcess.Start(ctx)

	// Wait for start process to actually start
	var startProcessStarted bool
	for !startProcessStarted {
		select {
		case event := <-startEvents:
			switch event {
			case EventStarted:
				c.events <- ComponentStarted
				startProcessStarted = true
			case EventFailed:
				c.events <- ComponentFailed
				return
			}
		case <-ctx.Done():
			c.events <- ComponentStopped
			return
		}
	}

	// If no ready command, emit ready immediately
	if len(c.config.ReadyCommand) == 0 {
		c.events <- ComponentReady
		// Continue monitoring start process
		c.monitorStartProcess(ctx, startEvents)
		return
	}

	// Start ready check process
	c.events <- ComponentChecking

	readyDone, err := c.startReadyProcess(ctx, startStdout, startStderr)
	if err != nil {
		c.events <- ComponentFailed
		c.startProcess.Stop()
		return
	}

	// Monitor both processes
	c.monitorProcessAndReadyChannel(ctx, startEvents, readyDone)
}

// startReadyProcess creates and starts the ready check process with piped input
func (c *Component) startReadyProcess(ctx context.Context, startStdout, startStderr io.ReadCloser) (chan error, error) {

	// Create ready command directly (not using process supervisor)
	readyCmd := exec.CommandContext(ctx, c.config.ReadyCommand[0], c.config.ReadyCommand[1:]...)

	readyStdin, err := readyCmd.StdinPipe()
	if err != nil {
		return nil, fmt.Errorf("failed to create ready stdin pipe: %w", err)
	}

	// Start the ready command
	if err := readyCmd.Start(); err != nil {
		readyStdin.Close()
		return nil, fmt.Errorf("failed to start ready command: %w", err)
	}

	// Create channel to pass stdin safely
	stdinCh := make(chan io.WriteCloser, 1)
	stdinCh <- readyStdin

	// Start piping in background
	go c.pipeOutput(ctx, startStdout, startStderr, stdinCh)

	// Monitor ready command completion
	readyDone := make(chan error, 1)
	go func() {
		err := readyCmd.Wait()
		readyDone <- err
		close(readyDone)
	}()

	return readyDone, nil
}

// pipeOutput safely pipes start process output to ready process input with non-blocking writes
func (c *Component) pipeOutput(ctx context.Context, stdout, stderr io.ReadCloser, stdinCh chan io.WriteCloser) {
	defer stdout.Close()
	defer stderr.Close()

	// Wait for stdin to be available
	var stdin io.WriteCloser
	select {
	case stdin = <-stdinCh:
		if stdin == nil {
			return // Ready process not available
		}
		// Don't defer close here - we'll close it explicitly when done
	case <-ctx.Done():
		return
	}

	// Use separate goroutines for stdout and stderr to avoid blocking
	var wg sync.WaitGroup
	wg.Add(2)

	// Pipe stdout
	go func() {
		defer wg.Done()
		scanner := bufio.NewScanner(stdout)
		for scanner.Scan() {
			line := scanner.Text()
			select {
			case <-ctx.Done():
				return
			default:
				if _, err := stdin.Write([]byte(line + "\n")); err != nil {
					return // Ready script stdin closed or errored
				}
			}
		}
	}()

	// Pipe stderr
	go func() {
		defer wg.Done()
		scanner := bufio.NewScanner(stderr)
		for scanner.Scan() {
			line := scanner.Text()
			select {
			case <-ctx.Done():
				return
			default:
				if _, err := stdin.Write([]byte(line + "\n")); err != nil {
					return // Ready script stdin closed or errored
				}
			}
		}
	}()

	// Wait for all piping to complete, then close stdin to signal EOF to ready script
	wg.Wait()
	stdin.Close()
}

// monitorStartProcess monitors only the start process (when no ready script)
func (c *Component) monitorStartProcess(ctx context.Context, startEvents <-chan EventType) {
	for {
		select {
		case event := <-startEvents:
			switch event {
			case EventExited:
				// Process completed successfully - this is normal for one-shot commands
				c.events <- ComponentStopped
				return
			case EventFailed:
				c.events <- ComponentFailed
				return
			case EventStopped:
				c.events <- ComponentStopped
				return
			}
		case <-ctx.Done():
			c.events <- ComponentStopped
			return
		}
	}
}

// monitorProcessAndReadyChannel monitors start process and ready command completion
func (c *Component) monitorProcessAndReadyChannel(ctx context.Context, startEvents <-chan EventType, readyDone <-chan error) {
	readyCompleted := false
	startProcessExited := false

	for {
		select {
		case event := <-startEvents:
			switch event {
			case EventFailed:
				// Start process failed - stop everything
				c.events <- ComponentFailed
				return
			case EventExited, EventStopped:
				// Start process exited
				if readyCompleted {
					// Ready script already completed successfully, so we can stop
					c.events <- ComponentStopped
					return
				} else {
					// Ready script still running, mark that start process exited
					startProcessExited = true
					// The ready script will determine final outcome
				}
			}

		case err := <-readyDone:
			if !readyCompleted {
				readyCompleted = true
				if err == nil {
					// Ready script completed successfully
					c.events <- ComponentReady

					// If start process already exited, we're done
					if startProcessExited {
						c.events <- ComponentStopped
						return
					}

					// Otherwise continue monitoring start process in the same goroutine
					readyCompleted = true
					// Continue in this loop to monitor start process
				} else {
					// Ready script failed - this means the component failed
					c.events <- ComponentFailed
					if !startProcessExited {
						c.startProcess.Stop()
					}
					return
				}
			}

		case <-ctx.Done():
			c.events <- ComponentStopped
			return
		}
	}
}
