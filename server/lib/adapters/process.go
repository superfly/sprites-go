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
	events          chan EventType
	signalCh        chan os.Signal
	stdoutBroadcast *outputBroadcaster
	stderrBroadcast *outputBroadcaster
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
		events:          make(chan EventType),
		signalCh:        make(chan os.Signal, 1),
		stdoutBroadcast: newOutputBroadcaster(os.Stdout),
		stderrBroadcast: newOutputBroadcaster(os.Stderr),
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
// It returns a channel that provides a stream of events.
func (p *Process) Start(ctx context.Context) <-chan EventType {
	go p.supervise(ctx)
	return p.events
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
	// Use a select to avoid blocking if the supervisor isn't running.
	select {
	case p.signalCh <- sig:
	default:
	}
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
	defer close(p.events)

	retries := 0
	shouldRestart := true // Control restart logic

	for {
		if !shouldRestart {
			return
		}

		p.events <- EventStarting

		if len(p.config.Command) == 0 {
			p.events <- EventFailed
			return
		}

		// Create command if not already created, or recreate for restart
		if p.cmd == nil {
			p.cmd = p.createCommand(ctx)
		}

		err := p.cmd.Start()
		if err != nil {
			p.events <- EventFailed
			return
		}

		p.events <- EventStarted

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
				p.events <- EventSignaled
				_ = p.cmd.Process.Signal(sig)
			case <-processExited:
				if ctx.Err() != nil {
					p.events <- EventStopped
					return
				}

				if shouldRestart && (p.config.MaxRetries == -1 || retries < p.config.MaxRetries) {
					p.events <- EventExited

					delay := p.config.RestartDelay * (1 << retries)
					retries++

					p.events <- EventRestarting

					// Reset command for restart (exec.Cmd can only be started once)
					p.cmd = nil

					select {
					case <-time.After(delay):
						// continue to next iteration of the outer for loop
						break processLoop
					case <-ctx.Done():
						p.events <- EventStopped
						return
					case sig := <-p.signalCh:
						isTerminating := sig == syscall.SIGINT || sig == syscall.SIGTERM || sig == syscall.SIGKILL
						if isTerminating {
							p.events <- EventStopping
							p.events <- EventStopped
							return
						}
						// Non-terminating signal during backoff - just log it
						p.events <- EventSignaled
					}
				} else {
					// Process exhausted retries or no retries configured
					if p.config.MaxRetries == 0 && retries == 0 {
						// No retries configured - natural completion is success
						p.events <- EventStopped
					} else if shouldRestart {
						// Retries were configured but exhausted - this is failure
						p.events <- EventFailed
					} else {
						// Explicitly stopped
						p.events <- EventStopped
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

	p.events <- EventStopping

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
			p.events <- EventStopped
		case <-time.After(p.config.GracefulShutdownTimeout):
			_ = cmd.Process.Kill()
			<-done // Wait for the process to die
			p.events <- EventStopped
		}
	} else {
		// No timeout configured, wait indefinitely
		<-done
		p.events <- EventStopped
	}
}
