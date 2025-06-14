package adapters

import (
	"bufio"
	"context"
	"fmt"
	"io"
	"os/exec"
	"sync"
)

// CmdComponentConfig holds configuration for a command-based component
// It implements the ComponentConfig interface
type CmdComponentConfig struct {
	StartCommand      []string               // Start script, REQUIRED
	ReadyCommand      []string               // Ready check script, nil if not available
	CheckpointCommand []string               // Checkpoint script, nil if not available
	RestoreCommand    []string               // Restore script, nil if not available
	EventHandlers     ComponentEventHandlers // Optional event handlers
}

// GetEventHandlers implements ComponentConfig interface
func (c CmdComponentConfig) GetEventHandlers() ComponentEventHandlers {
	return c.EventHandlers
}

// cmdComponent manages the lifecycle of a component using command execution
type cmdComponent struct {
	*BaseComponent // Embed shared event management
	config         CmdComponentConfig

	startProcess *Process
	startStdout  io.ReadCloser
	startStderr  io.ReadCloser
}

// NewCmdComponent creates a new command-based component manager
func NewCmdComponent(config CmdComponentConfig) Component {
	return &cmdComponent{
		BaseComponent: NewBaseComponent(config.GetEventHandlers()),
		config:        config,
	}
}

// Start initiates the component startup process
func (c *cmdComponent) Start(ctx context.Context) error {
	if len(c.config.StartCommand) == 0 {
		return fmt.Errorf("no start command configured")
	}

	// Start the supervision process
	go c.supervise(ctx)

	return nil
}

// Stop stops the component
func (c *cmdComponent) Stop() {
	if c.startProcess != nil {
		c.startProcess.Stop()
	}
}

// Checkpoint performs a checkpoint operation on the component
func (c *cmdComponent) Checkpoint(ctx context.Context) error {
	if len(c.config.CheckpointCommand) == 0 {
		return nil // No checkpoint command configured
	}

	// Use a simple synchronous approach for checkpoint/restore operations
	cmd := exec.CommandContext(ctx, c.config.CheckpointCommand[0], c.config.CheckpointCommand[1:]...)
	return cmd.Run()
}

// Restore performs a restore operation on the component
func (c *cmdComponent) Restore(ctx context.Context) error {
	if len(c.config.RestoreCommand) == 0 {
		return nil // No restore command configured
	}

	// Use a simple synchronous approach for checkpoint/restore operations
	cmd := exec.CommandContext(ctx, c.config.RestoreCommand[0], c.config.RestoreCommand[1:]...)
	return cmd.Run()
}

// supervise handles the component lifecycle
func (c *cmdComponent) supervise(ctx context.Context) {
	c.EmitEvent(ComponentStarting)

	// Create the main process with event handlers
	c.startProcess = NewProcess(ProcessConfig{
		Command:    c.config.StartCommand,
		MaxRetries: 0, // No auto-restart for components
		EventHandlers: ProcessEventHandlers{
			Started: func() {
				c.EmitEvent(ComponentStarted)
				c.handleProcessStarted(ctx)
			},
			Failed: func(err error) {
				c.EmitEvent(ComponentFailed, err)
			},
			Stopped: func() {
				c.EmitEvent(ComponentStopped)
			},
			Exited: func() {
				c.EmitEvent(ComponentStopped)
			},
		},
	})

	var startStdout, startStderr io.ReadCloser
	var err error

	// If we have a ready command, we need to capture the output for piping
	if len(c.config.ReadyCommand) > 0 {
		startStdout, err = c.startProcess.StdoutPipe()
		if err != nil {
			c.EmitEvent(ComponentFailed, err)
			return
		}
		startStderr, err = c.startProcess.StderrPipe()
		if err != nil {
			c.EmitEvent(ComponentFailed, err)
			return
		}
	}

	// Start the process
	err = c.startProcess.Start(ctx)
	if err != nil {
		c.EmitEvent(ComponentFailed, err)
		return
	}

	// Store stdout/stderr for ready check
	c.startStdout = startStdout
	c.startStderr = startStderr
}

// handleProcessStarted is called when the start process has started
func (c *cmdComponent) handleProcessStarted(ctx context.Context) {
	// If no ready command, emit ready immediately
	if len(c.config.ReadyCommand) == 0 {
		c.EmitEvent(ComponentReady)
		return
	}

	// Start ready check process
	c.EmitEvent(ComponentChecking)

	readyDone, err := c.startReadyProcess(ctx, c.startStdout, c.startStderr)
	if err != nil {
		c.EmitEvent(ComponentFailed, err)
		c.startProcess.Stop()
		return
	}

	// Monitor ready completion
	go func() {
		select {
		case err := <-readyDone:
			if err == nil {
				c.EmitEvent(ComponentReady)
			} else {
				c.EmitEvent(ComponentFailed, err)
				c.startProcess.Stop()
			}
		case <-ctx.Done():
			c.EmitEvent(ComponentStopped)
		}
	}()
}

// startReadyProcess creates and starts the ready check process with piped input
func (c *cmdComponent) startReadyProcess(ctx context.Context, startStdout, startStderr io.ReadCloser) (chan error, error) {

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
func (c *cmdComponent) pipeOutput(ctx context.Context, stdout, stderr io.ReadCloser, stdinCh chan io.WriteCloser) {
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
