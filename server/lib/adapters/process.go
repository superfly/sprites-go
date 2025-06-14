package adapters

import (
	"context"
	"fmt"
	"io"
	"os"
	"os/exec"
	"sync"
	"syscall"
	"time"
)

// EventType defines the type of event that can be emitted.
type EventType string

const (
	// EventStarting is emitted when the process is about to be started.
	EventStarting EventType = "starting"
	// EventStarted is emitted when the process has successfully started.
	EventStarted EventType = "started"
	// EventStopping is emitted when a stop sequence has been initiated.
	EventStopping EventType = "stopping"
	// EventStopped is emitted when the process has stopped.
	EventStopped EventType = "stopped"
	// EventSignaled is emitted when a signal is forwarded to the process.
	EventSignaled EventType = "signaled"
	// EventExited is emitted when the process exits and will be restarted.
	EventExited EventType = "exited"
	// EventRestarting is emitted when the process is about to be restarted.
	EventRestarting EventType = "restarting"
	// EventFailed is emitted when the process has failed permanently.
	EventFailed EventType = "failed"
)

// Typed Event Handler approach for processes
// Each event type has its own handler function signature
type (
	ProcessStarting   func()
	ProcessStarted    func()
	ProcessStopping   func()
	ProcessStopped    func()
	ProcessSignaled   func(os.Signal)
	ProcessExited     func()
	ProcessRestarting func()
	ProcessFailed     func(error)
)

// ProcessEventHandlers allows registering specific typed handlers for process events
type ProcessEventHandlers struct {
	Starting   ProcessStarting
	Started    ProcessStarted
	Stopping   ProcessStopping
	Stopped    ProcessStopped
	Signaled   ProcessSignaled
	Exited     ProcessExited
	Restarting ProcessRestarting
	Failed     ProcessFailed
}

// ProcessConfigInterface defines the interface for process configuration
// Implementations provide both configuration data and event handlers
type ProcessConfigInterface interface {
	// GetEventHandlers returns the event handlers (can be empty)
	GetEventHandlers() ProcessEventHandlers
}

// ProcessConfig holds the configuration for a supervised process.
type ProcessConfig struct {
	Command                 []string
	MaxRetries              int                  // Number of times to retry before giving up. -1 for infinite.
	RestartDelay            time.Duration        // Initial delay before a restart attempt. It will be doubled on each subsequent failure.
	GracefulShutdownTimeout time.Duration        // Timeout for graceful shutdown before force killing.
	EventHandlers           ProcessEventHandlers // Optional event handlers
}

// GetEventHandlers implements ProcessConfigInterface
func (pc ProcessConfig) GetEventHandlers() ProcessEventHandlers {
	return pc.EventHandlers
}

// Process is a supervisor for a single command.
type Process struct {
	config          ProcessConfig
	cmd             *exec.Cmd
	signalCh        chan os.Signal
	stdoutBroadcast *outputBroadcaster
	stderrBroadcast *outputBroadcaster
	handlers        ProcessEventHandlers
	lastSignal      os.Signal          // Track the last signal sent for handler callback
	ctx             context.Context    // Context for goroutine cleanup
	cancel          context.CancelFunc // Cancel function for cleanup
}

// outputBroadcaster manages broadcasting output to multiple subscribers
type outputBroadcaster struct {
	pipes        map[io.WriteCloser]bool
	mutex        sync.RWMutex
	parentWriter io.Writer
}

func newOutputBroadcaster(parentWriter io.Writer) *outputBroadcaster {
	return &outputBroadcaster{
		pipes:        make(map[io.WriteCloser]bool),
		parentWriter: parentWriter,
	}
}

func (ob *outputBroadcaster) newPipe() (io.ReadCloser, io.WriteCloser) {
	r, w := io.Pipe()

	ob.mutex.Lock()
	ob.pipes[w] = true
	ob.mutex.Unlock()

	// When the reader is closed, remove the writer from our map
	return &pipeReaderWrapper{ReadCloser: r, broadcaster: ob, writer: w}, w
}

func (ob *outputBroadcaster) removePipe(w io.WriteCloser) {
	ob.mutex.Lock()
	defer ob.mutex.Unlock()

	if ob.pipes[w] {
		delete(ob.pipes, w)
		w.Close()
	}
}

func (ob *outputBroadcaster) closeAll() {
	ob.mutex.Lock()
	defer ob.mutex.Unlock()

	for pipe := range ob.pipes {
		pipe.Close()
		delete(ob.pipes, pipe)
	}
}

func (ob *outputBroadcaster) broadcast(data []byte) {
	// Always write to parent first - this MUST succeed
	ob.parentWriter.Write(data)

	ob.mutex.Lock()
	defer ob.mutex.Unlock()

	// Broadcast to all pipes, removing any that fail
	var toRemove []io.WriteCloser
	for pipe := range ob.pipes {
		_, err := pipe.Write(data)
		if err != nil {
			// Pipe errored or closed, mark for removal
			toRemove = append(toRemove, pipe)
		}
	}

	// Remove failed pipes
	for _, pipe := range toRemove {
		delete(ob.pipes, pipe)
		pipe.Close()
	}
}

// pipeReaderWrapper wraps a pipe reader to clean up when closed
type pipeReaderWrapper struct {
	io.ReadCloser
	broadcaster *outputBroadcaster
	writer      io.WriteCloser
}

func (prw *pipeReaderWrapper) Close() error {
	prw.broadcaster.removePipe(prw.writer)
	return prw.ReadCloser.Close()
}

// NewProcess creates a new process supervisor.
func NewProcess(config ProcessConfig) *Process {
	return &Process{
		config:          config,
		cmd:             nil, // Will be created when needed
		signalCh:        make(chan os.Signal, 1),
		stdoutBroadcast: newOutputBroadcaster(os.Stdout),
		stderrBroadcast: newOutputBroadcaster(os.Stderr),
		handlers:        config.EventHandlers,
	}
}

// EmitEvent calls the corresponding handler if set
func (p *Process) EmitEvent(event EventType, err ...error) {
	// Call handler if set (type-safe approach)
	// Run handler in a goroutine to avoid blocking the supervisor
	// Use context to ensure proper cleanup
	if p.ctx != nil {
		go func() {
			// Check if context is canceled before running handler
			select {
			case <-p.ctx.Done():
				return // Context canceled, don't run handler
			default:
			}

			switch event {
			case EventStarting:
				if p.handlers.Starting != nil {
					p.handlers.Starting()
				}
			case EventStarted:
				if p.handlers.Started != nil {
					p.handlers.Started()
				}
			case EventStopping:
				if p.handlers.Stopping != nil {
					p.handlers.Stopping()
				}
			case EventStopped:
				if p.handlers.Stopped != nil {
					p.handlers.Stopped()
				}
			case EventSignaled:
				if p.handlers.Signaled != nil {
					p.handlers.Signaled(p.lastSignal)
				}
			case EventExited:
				if p.handlers.Exited != nil {
					p.handlers.Exited()
				}
			case EventRestarting:
				if p.handlers.Restarting != nil {
					p.handlers.Restarting()
				}
			case EventFailed:
				if p.handlers.Failed != nil {
					var failErr error
					if len(err) > 0 {
						failErr = err[0]
					}
					p.handlers.Failed(failErr)
				}
			}
		}()
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
	if p.config.MaxRetries != 0 {
		return nil, fmt.Errorf("stdout pipe not compatible with auto-restart (MaxRetries=%d)", p.config.MaxRetries)
	}
	reader, _ := p.stdoutBroadcast.newPipe()
	return reader, nil
}

// StderrPipe returns a pipe that will be connected to the command's standard error when the command starts.
// The output will also continue to go to os.Stderr. This maintains backward compatibility.
// The pipe will continue to receive data even across process restarts.
func (p *Process) StderrPipe() (io.ReadCloser, error) {
	if p.config.MaxRetries != 0 {
		return nil, fmt.Errorf("stderr pipe not compatible with auto-restart (MaxRetries=%d)", p.config.MaxRetries)
	}
	reader, _ := p.stderrBroadcast.newPipe()
	return reader, nil
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
	// Use a select to avoid blocking if the supervisor isn't running.
	select {
	case p.signalCh <- sig:
	default:
	}
}

// SetEventHandlers sets up Observer pattern callbacks for process events
func (p *Process) SetEventHandlers(handlers ProcessEventHandlers) {
	p.handlers = handlers
}

func (p *Process) createCommand(ctx context.Context) *exec.Cmd {
	cmd := exec.CommandContext(ctx, p.config.Command[0], p.config.Command[1:]...)

	// Set up the process in its own process group for better signal isolation
	// cmd.SysProcAttr = &syscall.SysProcAttr{
	// 	Setpgid: true,
	// }

	// Set up pipes to capture stdout/stderr and broadcast them
	stdoutPipe, err := cmd.StdoutPipe()
	if err == nil {
		go p.broadcastFromPipe(stdoutPipe, p.stdoutBroadcast)
	}

	stderrPipe, err := cmd.StderrPipe()
	if err == nil {
		go p.broadcastFromPipe(stderrPipe, p.stderrBroadcast)
	}

	return cmd
}

// broadcastFromPipe reads from a pipe and broadcasts to all subscribers
func (p *Process) broadcastFromPipe(pipe io.ReadCloser, broadcaster *outputBroadcaster) {
	defer pipe.Close()
	defer broadcaster.closeAll() // Close all subscriber pipes when source ends

	buf := make([]byte, 4096)
	for {
		n, err := pipe.Read(buf)
		if n > 0 {
			data := make([]byte, n)
			copy(data, buf[:n])
			broadcaster.broadcast(data)
		}
		if err != nil {
			break
		}
	}
}

func (p *Process) supervise(ctx context.Context) {
	defer close(p.signalCh)

	// Create an independent context for event handlers to avoid premature cancellation
	// This ensures event handlers can run even when the main context is canceled
	p.ctx, p.cancel = context.WithCancel(context.Background())
	defer func() {
		if p.cancel != nil {
			p.cancel() // Clean up any remaining event handler goroutines
		}
	}()

	retries := 0
	shouldRestart := true // Control restart logic

	for {
		if !shouldRestart {
			return
		}

		p.EmitEvent(EventStarting)

		if len(p.config.Command) == 0 {
			p.EmitEvent(EventFailed)
			time.Sleep(time.Millisecond)
			return
		}

		// Create command if not already created, or recreate for restart
		if p.cmd == nil {
			p.cmd = p.createCommand(ctx)
		}

		err := p.cmd.Start()
		if err != nil {
			p.EmitEvent(EventFailed, err)
			time.Sleep(time.Millisecond)
			return
		}

		p.EmitEvent(EventStarted)

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
				if isTerminating && shouldRestart {
					shouldRestart = false // Prevent restart
					p.stopOrKill(p.cmd, sig)
					return // Stop supervising
				}

				// Non-terminating signal - just forward it
				p.EmitEvent(EventSignaled)
				_ = p.cmd.Process.Signal(sig)
			case <-ctx.Done():
				// Context was cancelled - emit EventStopped first, then stop process
				p.EmitEvent(EventStopped)
				time.Sleep(time.Millisecond) // Ensure handler runs

				// Now stop the process
				if p.cmd.Process != nil {
					_ = p.cmd.Process.Signal(syscall.SIGTERM)

					// Wait briefly for graceful exit
					done := make(chan struct{})
					go func() {
						_, _ = p.cmd.Process.Wait()
						close(done)
					}()

					select {
					case <-done:
						// Process exited gracefully
					case <-time.After(100 * time.Millisecond):
						// Force kill if it doesn't exit quickly
						_ = p.cmd.Process.Kill()
						<-done
					}
				}
				return
			case <-processExited:
				if ctx.Err() != nil {
					p.EmitEvent(EventStopped)
					time.Sleep(time.Millisecond)
					return
				}

				if shouldRestart && (p.config.MaxRetries == -1 || retries < p.config.MaxRetries) {
					p.EmitEvent(EventExited)

					// Only increment retries if we're actually going to retry
					retries++
					delay := p.config.RestartDelay * (1 << (retries - 1))

					p.EmitEvent(EventRestarting)

					// Reset command for restart (exec.Cmd can only be started once)
					p.cmd = nil

					select {
					case <-time.After(delay):
						// continue to next iteration of the outer for loop
						break processLoop
					case <-ctx.Done():
						p.EmitEvent(EventStopped)
						time.Sleep(time.Millisecond)
						return
					case sig := <-p.signalCh:
						p.lastSignal = sig // Track signal for callbacks
						isTerminating := sig == syscall.SIGINT || sig == syscall.SIGTERM || sig == syscall.SIGKILL
						if isTerminating {
							p.EmitEvent(EventStopping)
							p.EmitEvent(EventStopped)
							time.Sleep(time.Millisecond)
							return
						}
						// Non-terminating signal during backoff - just log it
						p.EmitEvent(EventSignaled)
					}
				} else {
					// Process exhausted retries or no retries configured
					if p.config.MaxRetries == 0 && retries == 0 {
						// No retries configured - natural completion is success
						p.EmitEvent(EventStopped)
						// Small delay to ensure handler goroutine runs before context is canceled
						time.Sleep(time.Millisecond)
					} else if shouldRestart {
						// Retries were configured but exhausted - this is failure
						p.EmitEvent(EventFailed)
						time.Sleep(time.Millisecond)
					} else {
						// Explicitly stopped
						p.EmitEvent(EventStopped)
						time.Sleep(time.Millisecond)
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

	p.EmitEvent(EventStopping)

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
			p.EmitEvent(EventStopped)
			time.Sleep(time.Millisecond)
		case <-time.After(p.config.GracefulShutdownTimeout):
			_ = cmd.Process.Kill()
			<-done // Wait for the process to die
			p.EmitEvent(EventStopped)
			time.Sleep(time.Millisecond)
		}
	} else {
		// No timeout configured, wait indefinitely
		<-done
		p.EmitEvent(EventStopped)
		time.Sleep(time.Millisecond)
	}
}
