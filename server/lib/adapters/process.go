package adapters

import (
	"context"
	"fmt"
	"io"
	"os"
	"os/exec"
	"sprite-env/lib"
	"sync"
	"syscall"
	"time"
)

// ProcessEventType defines the type of event that can be emitted.
type ProcessEventType string

const (
	// ProcessStartingEvent is emitted when the process is about to be started.
	ProcessStartingEvent ProcessEventType = "starting"
	// ProcessStartedEvent is emitted when the process has successfully started.
	ProcessStartedEvent ProcessEventType = "started"
	// ProcessStoppingEvent is emitted when a stop sequence has been initiated.
	ProcessStoppingEvent ProcessEventType = "stopping"
	// ProcessStoppedEvent is emitted when the process has stopped.
	ProcessStoppedEvent ProcessEventType = "stopped"
	// ProcessSignaledEvent is emitted when a signal is forwarded to the process.
	ProcessSignaledEvent ProcessEventType = "signaled"
	// ProcessExitedEvent is emitted when the process exits and will be restarted.
	ProcessExitedEvent ProcessEventType = "exited"
	// ProcessRestartingEvent is emitted when the process is about to be restarted.
	ProcessRestartingEvent ProcessEventType = "restarting"
	// ProcessFailedEvent is emitted when the process has failed permanently.
	ProcessFailedEvent ProcessEventType = "failed"
)

// ProcessConfig holds the configuration for a supervised process.
type ProcessConfig struct {
	Command                 []string
	MaxRetries              int           // Number of times to retry before giving up. -1 for infinite.
	RestartDelay            time.Duration // Initial delay before a restart attempt. It will be doubled on each subsequent failure.
	GracefulShutdownTimeout time.Duration // Timeout for graceful shutdown before force killing.
}

// Process is a supervisor for a single command.
type Process struct {
	config          ProcessConfig
	cmd             *exec.Cmd
	signalCh        chan os.Signal // Unbuffered - supervisor always ready to receive, no signals dropped
	signalChClosed  bool           // Track if signal channel is closed
	signalChMutex   sync.RWMutex   // Protect access to signalChClosed flag
	stdoutMultiPipe *lib.MultiPipe
	stderrMultiPipe *lib.MultiPipe
	eventCh         chan ProcessEventType // Buffered - external resource with unpredictable timing, consumers need reliable delivery
	lastSignal      os.Signal             // Track the last signal sent for handler callback
	ctx             context.Context       // Context for goroutine cleanup
	cancel          context.CancelFunc    // Cancel function for cleanup
}

// NewProcess creates a new process supervisor.
func NewProcess(config ProcessConfig) *Process {
	return &Process{
		config:          config,
		cmd:             nil,                             // Will be created when needed
		signalCh:        make(chan os.Signal),            // Unbuffered channel
		stdoutMultiPipe: lib.NewMultiPipe(4096),          // 4KB buffer per reader
		stderrMultiPipe: lib.NewMultiPipe(4096),          // 4KB buffer per reader
		eventCh:         make(chan ProcessEventType, 10), // Buffered channel with some buffer
	}
}

// Events returns the channel for listening to process events
func (p *Process) Events() <-chan ProcessEventType {
	return p.eventCh
}

// EmitEvent sends an event to the channel
func (p *Process) EmitEvent(event ProcessEventType, err ...error) {
	// Emit events synchronously to guarantee ordering, especially important for
	// terminal events like ProcessFailedEvent that should be the final event
	if p.ctx != nil {
		select {
		case <-p.ctx.Done():
			return // Context canceled, don't emit event
		case p.eventCh <- event:
			// Event sent successfully - synchronous to maintain order
		}
	}
}

// StdinPipe returns a pipe that will be connected to the command's standard input when the command starts.
// This is not compatible with auto-restart functionality.
func (p *Process) StdinPipe() (io.WriteCloser, error) {
	if p.config.MaxRetries != 0 {
		return nil, fmt.Errorf("stdin pipe not compatible with auto-restart (MaxRetries=%d)", p.config.MaxRetries)
	}
	if p.cmd == nil {
		p.cmd = p.createCommand(context.Background())
	}
	return p.cmd.StdinPipe()
}

// StdoutPipe returns a pipe that will be connected to the command's standard output when the command starts.
// The output will also continue to go to os.Stdout. This maintains backward compatibility.
// The pipe will continue to receive data even across process restarts.
func (p *Process) StdoutPipe() (io.ReadCloser, error) {
	return p.stdoutMultiPipe.NewReader(), nil
}

// StderrPipe returns a pipe that will be connected to the command's standard error when the command starts.
// The output will also continue to go to os.Stderr. This maintains backward compatibility.
// The pipe will continue to receive data even across process restarts.
func (p *Process) StderrPipe() (io.ReadCloser, error) {
	return p.stderrMultiPipe.NewReader(), nil
}

// Start begins supervising the process in a new goroutine.
func (p *Process) Start(ctx context.Context) error {
	go p.supervise(ctx)
	return nil
}

// Stop signals the process to terminate gracefully. If the process does not
// stop within the configured timeout, it is forcefully killed.
func (p *Process) Stop() {
	p.Signal(syscall.SIGTERM)
}

// Signal sends an OS signal to the supervised process.
// If the signal is SIGINT, SIGTERM, or SIGKILL, the process will be treated as if Stop()
// was called, meaning it will not be restarted.
func (p *Process) Signal(sig os.Signal) {
	p.lastSignal = sig // Track the signal for handler callbacks

	// Check if signal channel is closed to avoid panic
	p.signalChMutex.RLock()
	closed := p.signalChClosed
	p.signalChMutex.RUnlock()

	if closed {
		return // Channel is closed, can't send signal
	}

	// Send signal to supervisor - use select to avoid blocking on closed channel
	select {
	case p.signalCh <- sig:
		// Signal sent successfully
	default:
		// Channel is full or closed, signal couldn't be sent
		// This can happen during shutdown races - not a critical error
	}
}

func (p *Process) createCommand(ctx context.Context) *exec.Cmd {
	cmd := exec.CommandContext(ctx, p.config.Command[0], p.config.Command[1:]...)

	// Inherit all system environment variables
	cmd.Env = os.Environ()

	// Set up the process in its own process group for better signal isolation
	// cmd.SysProcAttr = &syscall.SysProcAttr{
	// 	Setpgid: true,
	// }

	// Use MultiWriter to send output to both parent and multipipe
	cmd.Stdout = io.MultiWriter(os.Stdout, p.stdoutMultiPipe)
	cmd.Stderr = io.MultiWriter(os.Stderr, p.stderrMultiPipe)

	return cmd
}

func (p *Process) supervise(ctx context.Context) {
	// Create an independent context for event handlers FIRST, before any event emission
	// This ensures event handlers can run even when the main context is canceled
	p.ctx, p.cancel = context.WithCancel(context.Background())

	defer func() {
		// Mark channel as closed and then close it (check flag to prevent double-close)
		p.signalChMutex.Lock()
		if !p.signalChClosed {
			p.signalChClosed = true
			close(p.signalCh)
		}
		p.signalChMutex.Unlock()

		// Close the event channel to signal no more events will be sent
		close(p.eventCh)

		// Clean up event handler goroutines
		if p.cancel != nil {
			p.cancel()
		}

		// Close multipipes
		p.stdoutMultiPipe.Close()
		p.stderrMultiPipe.Close()
	}()

	retries := 0
	shouldRestart := true // Control restart logic

	for {
		if !shouldRestart {
			return
		}

		p.EmitEvent(ProcessStartingEvent)

		if len(p.config.Command) == 0 {
			p.EmitEvent(ProcessFailedEvent)
			return
		}

		// Create command if not already created, or recreate for restart
		if p.cmd == nil {
			p.cmd = p.createCommand(ctx)
		}

		err := p.cmd.Start()
		if err != nil {
			p.EmitEvent(ProcessFailedEvent, err)
			return
		}

		p.EmitEvent(ProcessStartedEvent)

		processExited := make(chan error, 1)
		go func() {
			processExited <- p.cmd.Wait()
		}()

	processLoop:
		for {
			select {
			case sig := <-p.signalCh:
				if p.cmd.Process == nil {
					continue
				}

				isTerminating := sig == syscall.SIGINT || sig == syscall.SIGTERM || sig == syscall.SIGKILL
				if isTerminating {
					// Always handle terminating signals with proper stopping sequence
					shouldRestart = false // Prevent restart
					p.stopOrKill(p.cmd, sig)
					return // Stop supervising
				}

				// Non-terminating signal - just forward it
				p.EmitEvent(ProcessSignaledEvent)
				_ = p.cmd.Process.Signal(sig)
			case <-ctx.Done():
				// Context was cancelled - stop process (stopOrKill will emit ProcessStoppedEvent)
				if p.cmd.Process != nil {
					p.stopOrKill(p.cmd, syscall.SIGTERM)
				}
				return
			case <-processExited:
				if ctx.Err() != nil {
					// Context was cancelled - the context cancellation handler will emit ProcessStoppedEvent
					return
				}

				if shouldRestart && (p.config.MaxRetries == -1 || retries < p.config.MaxRetries) {
					// Process will restart - emit ProcessRestartingEvent directly, not ProcessExitedEvent
					// ProcessExitedEvent would put state machine in terminal "Exited" state which can't transition back
					p.EmitEvent(ProcessRestartingEvent)

					// Only increment retries if we're actually going to retry
					retries++
					delay := p.config.RestartDelay * (1 << (retries - 1))

					// Reset command for restart (exec.Cmd can only be started once)
					p.cmd = nil

					select {
					case <-time.After(delay):
						// continue to next iteration of the outer for loop
						break processLoop
					case <-ctx.Done():
						// Context was cancelled - the context cancellation handler will emit ProcessStoppedEvent
						return
					case sig := <-p.signalCh:
						p.lastSignal = sig // Track signal for callbacks
						isTerminating := sig == syscall.SIGINT || sig == syscall.SIGTERM || sig == syscall.SIGKILL
						if isTerminating {
							// Process already exited, just need to stop restarting
							shouldRestart = false
							p.EmitEvent(ProcessStoppingEvent)
							p.EmitEvent(ProcessStoppedEvent)
							return
						}
						// Non-terminating signal during backoff - just log it
						p.EmitEvent(ProcessSignaledEvent)
					}
				} else {
					// Process exited and no restart configured/retries exhausted
					// Distinguish between external clean exit vs external error exit
					exitCode := 0
					if p.cmd.ProcessState != nil {
						exitCode = p.cmd.ProcessState.ExitCode()
					}

					if exitCode == 0 {
						// Clean external exit (code 0) - natural completion
						p.EmitEvent(ProcessStoppedEvent)
					} else {
						// Error external exit (code ≠ 0) - failure
						p.EmitEvent(ProcessFailedEvent, fmt.Errorf("process exited with code %d", exitCode))
					}

					return
				}
			}
		}
	}
}

func (p *Process) stopOrKill(cmd *exec.Cmd, sig os.Signal) {
	if cmd.Process == nil {
		return
	}

	// Check if process is already dead before trying to stop it
	// If the process has already exited, don't emit stopping/stopped events
	if cmd.ProcessState != nil && cmd.ProcessState.Exited() {
		return
	}

	p.EmitEvent(ProcessStoppingEvent)

	_ = cmd.Process.Signal(sig)

	done := make(chan struct{})
	go func() {
		_, _ = cmd.Process.Wait()
		close(done)
	}()

	// Wait for graceful exit or timeout
	if p.config.GracefulShutdownTimeout > 0 {
		select {
		case <-done:
			p.EmitEvent(ProcessStoppedEvent)
		case <-time.After(p.config.GracefulShutdownTimeout):
			_ = cmd.Process.Kill()
			<-done // Wait for the process to die
			p.EmitEvent(ProcessStoppedEvent)
		}
	} else {
		// No timeout configured, wait indefinitely
		<-done
		p.EmitEvent(ProcessStoppedEvent)
	}
}

// Close permanently disposes of the process and all its resources
// This implements the io.Closer interface for proper resource cleanup
func (p *Process) Close() error {
	// Cancel the context to make supervise() exit and handle all cleanup
	if p.cancel != nil {
		p.cancel()
	}
	return nil
}
