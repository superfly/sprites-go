package adapters

import (
	"bufio"
	"context"
	"fmt"
	"io"
	"os"
	"os/exec"
	"time"
)

// CmdComponentConfig holds configuration for a command-based component
type CmdComponentConfig struct {
	Name              string        // Component name for identification
	StartCommand      []string      // Start script, REQUIRED
	ReadyCommand      []string      // Ready check script, nil if not available
	CheckpointCommand []string      // Checkpoint script, nil if not available
	RestoreCommand    []string      // Restore script, nil if not available
	ReadyTimeout      time.Duration // Timeout for ready check, defaults to 10s if zero
}

// cmdComponent manages the lifecycle of a component using command execution
type cmdComponent struct {
	*BaseComponent // Embed shared event management
	config         CmdComponentConfig

	startProcess *Process
	ctx          context.Context
	cancel       context.CancelFunc
}

// NewCmdComponent creates a new command-based component manager
func NewCmdComponent(config CmdComponentConfig) Component {
	ctx, cancel := context.WithCancel(context.Background())
	return &cmdComponent{
		BaseComponent: NewBaseComponent(ctx),
		config:        config,
		ctx:           ctx,
		cancel:        cancel,
	}
}

// GetName returns the component name
func (c *cmdComponent) GetName() string {
	return c.config.Name
}

// Start initiates the component startup process
func (c *cmdComponent) Start(ctx context.Context) error {
	if len(c.config.StartCommand) == 0 {
		return fmt.Errorf("no start command configured")
	}

	// Start the supervision process
	go c.supervise()

	return nil
}

// Stop stops the component
func (c *cmdComponent) Stop() {
	if c.startProcess != nil {
		c.startProcess.Stop()
	}
}

// Close permanently disposes of the component and all its resources
func (c *cmdComponent) Close() error {
	// First stop the component
	c.Stop()

	// Close the underlying process
	if c.startProcess != nil {
		c.startProcess.Close()
	}

	// Cancel the context to stop all goroutines
	if c.cancel != nil {
		c.cancel()
	}

	// Close the base component (event channel)
	return c.BaseComponent.Close()
}

// Checkpoint performs a checkpoint operation on the component
func (c *cmdComponent) Checkpoint(checkpointID string) error {
	if len(c.config.CheckpointCommand) == 0 {
		return nil // No checkpoint command configured
	}

	// Use a simple synchronous approach for checkpoint/restore operations
	cmd := exec.CommandContext(c.ctx, c.config.CheckpointCommand[0], c.config.CheckpointCommand[1:]...)

	// Inherit existing environment and add checkpoint ID
	cmd.Env = os.Environ()
	if checkpointID != "" {
		cmd.Env = append(cmd.Env, fmt.Sprintf("CHECKPOINT_ID=%s", checkpointID))
	}

	return cmd.Run()
}

// Restore performs a restore operation on the component
func (c *cmdComponent) Restore(checkpointID string) error {
	if len(c.config.RestoreCommand) == 0 {
		return nil // No restore command configured
	}

	// Use a simple synchronous approach for checkpoint/restore operations
	cmd := exec.CommandContext(c.ctx, c.config.RestoreCommand[0], c.config.RestoreCommand[1:]...)

	// Inherit existing environment and add checkpoint ID
	cmd.Env = os.Environ()
	if checkpointID != "" {
		cmd.Env = append(cmd.Env, fmt.Sprintf("CHECKPOINT_ID=%s", checkpointID))
	}

	return cmd.Run()
}

// supervise handles the component lifecycle
func (c *cmdComponent) supervise() {
	c.EmitEvent(ComponentStarting)

	// Create the main process with event handlers
	c.startProcess = NewProcess(ProcessConfig{
		Command:                 c.config.StartCommand,
		MaxRetries:              0,               // No auto-restart for components
		GracefulShutdownTimeout: 2 * time.Second, // Reasonable timeout for tests
	})

	// Start the process
	err := c.startProcess.Start(c.ctx)
	if err != nil {
		c.EmitEvent(ComponentFailed)
		return
	}

	// Listen for process events and translate them to component events
	go c.listenForProcessEvents()
}

// listenForProcessEvents listens to process events and translates them to component events
func (c *cmdComponent) listenForProcessEvents() {
	events := c.startProcess.Events()
	for {
		select {
		case <-c.ctx.Done():
			return
		case event := <-events:
			switch event {
			case ProcessStartedEvent:
				c.EmitEventSync(ComponentStarted)
				c.handleProcessStarted()
			case ProcessFailedEvent:
				c.EmitEvent(ComponentFailed)
			case ProcessStoppedEvent:
				c.EmitEvent(ComponentStopped)
			}
		}
	}
}

// handleProcessStarted is called when the start process has started
func (c *cmdComponent) handleProcessStarted() {
	// If no ready command, emit ready immediately
	if len(c.config.ReadyCommand) == 0 {
		c.EmitEventSync(ComponentReady)
		return
	}

	// Start ready check process
	c.EmitEvent(ComponentChecking)

	readyDone, readyCmd, err := c.startReadyProcess()
	if err != nil {
		c.EmitEvent(ComponentFailed)
		return
	}

	// Set default timeout if not specified
	timeout := c.config.ReadyTimeout
	if timeout == 0 {
		timeout = 10 * time.Second
	}

	// Monitor ready completion with timeout in a single goroutine
	go func() {
		select {
		case err := <-readyDone:
			if err == nil {
				c.EmitEvent(ComponentReady)
			} else {
				c.EmitEvent(ComponentFailed)
			}
		case <-time.After(timeout):
			// Timeout occurred - kill the ready process and emit failure
			if readyCmd != nil && readyCmd.Process != nil {
				readyCmd.Process.Kill()
			}
			c.EmitEvent(ComponentFailed)
			return // Exit immediately, don't wait for context cancellation
		case <-c.ctx.Done():
			c.EmitEvent(ComponentStopped)
		}
	}()
}

// startReadyProcess creates and starts the ready check process with piped input
func (c *cmdComponent) startReadyProcess() (chan error, *exec.Cmd, error) {
	// Get pipes from the start process
	stdoutReader, err := c.startProcess.StdoutPipe()
	if err != nil {
		return nil, nil, fmt.Errorf("failed to get stdout pipe: %w", err)
	}

	stderrReader, err := c.startProcess.StderrPipe()
	if err != nil {
		stdoutReader.Close()
		return nil, nil, fmt.Errorf("failed to get stderr pipe: %w", err)
	}

	// Create ready command directly (not using process supervisor)
	readyCmd := exec.CommandContext(c.ctx, c.config.ReadyCommand[0], c.config.ReadyCommand[1:]...)

	// Get stdin pipe for ready command
	readyStdin, err := readyCmd.StdinPipe()
	if err != nil {
		stdoutReader.Close()
		stderrReader.Close()
		return nil, nil, fmt.Errorf("failed to create stdin pipe: %w", err)
	}

	// Start the ready command
	if err := readyCmd.Start(); err != nil {
		stdoutReader.Close()
		stderrReader.Close()
		readyStdin.Close()
		return nil, nil, fmt.Errorf("failed to start ready command: %w", err)
	}

	// Create pipes to merge stdout and stderr
	pipeReader, pipeWriter := io.Pipe()

	// Pipe stdout and stderr to the pipe writer
	go func() {
		scanner := bufio.NewScanner(stdoutReader)
		for scanner.Scan() {
			pipeWriter.Write([]byte(scanner.Text() + "\n"))
		}
		stdoutReader.Close()
	}()

	go func() {
		scanner := bufio.NewScanner(stderrReader)
		for scanner.Scan() {
			pipeWriter.Write([]byte(scanner.Text() + "\n"))
		}
		stderrReader.Close()
		pipeWriter.Close() // Close after both are done
	}()

	// Copy from pipe to ready stdin
	go func() {
		io.Copy(readyStdin, pipeReader)
		readyStdin.Close()
		pipeReader.Close()
	}()

	// Monitor ready command completion
	readyDone := make(chan error, 1)
	go func() {
		err := readyCmd.Wait()
		readyDone <- err
		close(readyDone)
	}()

	return readyDone, readyCmd, nil
}
