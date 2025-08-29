// Package supervisor provides a simple, robust process supervisor with graceful shutdown.
package supervisor

import (
	"context"
	"errors"
	"fmt"
	"io"
	"log/slog"
	"os"
	"os/exec"
	"sync"
	"syscall"
	"time"
)

// Supervisor manages a single process with graceful shutdown and signal forwarding
type Supervisor struct {
	cmd             *exec.Cmd
	gracePeriod     time.Duration
	startedCh       chan struct{}
	stoppedCh       chan struct{}
	errorCh         chan error
	signalCh        chan os.Signal
	stopCh          chan struct{}
	ctx             context.Context
	cancel          context.CancelFunc
	stdoutMultiPipe *MultiPipe
	stderrMultiPipe *MultiPipe
	waitErr         error
	waitOnce        sync.Once
	logger          *slog.Logger
}

// Config holds configuration for the supervisor
type Config struct {
	Command     string
	Args        []string
	GracePeriod time.Duration
	Env         []string
	Dir         string
	Logger      *slog.Logger // Optional logger
}

// New creates a new supervisor instance
func New(config Config) (*Supervisor, error) {
	if config.Command == "" {
		return nil, errors.New("command cannot be empty")
	}

	if config.GracePeriod <= 0 {
		config.GracePeriod = 10 * time.Second
	}

	// Set up logger
	logger := config.Logger
	if logger == nil {
		// Create a no-op logger that discards all output
		logger = slog.New(slog.NewTextHandler(io.Discard, nil))
	}

	ctx, cancel := context.WithCancel(context.Background())
	cmd := exec.CommandContext(ctx, config.Command, config.Args...)

	if len(config.Env) > 0 {
		cmd.Env = config.Env
	}
	if config.Dir != "" {
		cmd.Dir = config.Dir
	}

	// Set process group to enable killing child processes
	cmd.SysProcAttr = &syscall.SysProcAttr{
		Setpgid: true,
	}

	// Create multipipes for stdout/stderr
	stdoutMultiPipe := NewMultiPipe(4096) // 4KB buffer per reader
	stderrMultiPipe := NewMultiPipe(4096) // 4KB buffer per reader

	// Set up process output to go to both os.Stdout/os.Stderr and multipipes
	cmd.Stdout = io.MultiWriter(os.Stdout, stdoutMultiPipe)
	cmd.Stderr = io.MultiWriter(os.Stderr, stderrMultiPipe)

	return &Supervisor{
		cmd:             cmd,
		gracePeriod:     config.GracePeriod,
		startedCh:       make(chan struct{}),
		stoppedCh:       make(chan struct{}),
		errorCh:         make(chan error, 1),
		signalCh:        make(chan os.Signal, 10),
		stopCh:          make(chan struct{}),
		ctx:             ctx,
		cancel:          cancel,
		stdoutMultiPipe: stdoutMultiPipe,
		stderrMultiPipe: stderrMultiPipe,
		logger:          logger,
	}, nil
}

// Start starts the supervised process and returns its PID
func (s *Supervisor) Start() (int, error) {
	// Prevent multiple starts
	select {
	case <-s.startedCh:
		return -1, errors.New("process already started")
	default:
	}

	// Log the command being executed for debugging
	s.logger.Info("Starting process",
		"command", s.cmd.Path,
		"args", s.cmd.Args,
		"dir", s.cmd.Dir)

	// Start the process
	if err := s.cmd.Start(); err != nil {
		// Log additional debugging information for command not found errors
		if exitErr, ok := err.(*exec.Error); ok {
			s.logger.Error("Failed to start process",
				"error", err,
				"command", s.cmd.Path,
				"lookup_error", exitErr.Err,
				"type", "exec_error")
		}
		return -1, fmt.Errorf("failed to start process: %w", err)
	}

	close(s.startedCh)
	go s.monitor()

	return s.cmd.Process.Pid, nil
}

// Stop gracefully stops the process with SIGTERM, then SIGKILL after grace period
func (s *Supervisor) Stop() error {
	select {
	case <-s.stoppedCh:
		return nil // Already stopped
	case <-s.startedCh:
		// Process was started, proceed with stop
	default:
		return errors.New("process not started")
	}

	// Check if stop was already initiated
	select {
	case <-s.stopCh:
		// Stop already initiated, just wait
	default:
		// Initiate stop
		close(s.stopCh)
	}

	// Wait for process to stop or timeout
	select {
	case <-s.stoppedCh:
		return nil
	case <-time.After(s.gracePeriod + time.Second):
		return errors.New("process stop timeout")
	}
}

// Signal forwards a signal to the supervised process
func (s *Supervisor) Signal(sig os.Signal) error {
	select {
	case <-s.startedCh:
		// Process is started
	default:
		return errors.New("process not started")
	}

	select {
	case <-s.stoppedCh:
		return errors.New("process already stopped")
	case s.signalCh <- sig:
		return nil
	case <-time.After(100 * time.Millisecond):
		return errors.New("signal channel full")
	}
}

// Wait blocks until the process exits
func (s *Supervisor) Wait() error {
	select {
	case <-s.startedCh:
		// Process was started
	default:
		return errors.New("process not started")
	}

	// Wait for process to stop
	<-s.stoppedCh

	// Ensure we only read from errorCh once
	s.waitOnce.Do(func() {
		select {
		case err := <-s.errorCh:
			s.waitErr = err
		default:
			s.waitErr = nil
		}
	})

	return s.waitErr
}

// Pid returns the process ID of the supervised process
func (s *Supervisor) Pid() (int, error) {
	select {
	case <-s.startedCh:
		// Process is started
	default:
		return -1, errors.New("process not started")
	}

	if s.cmd.Process == nil {
		return -1, errors.New("process handle is nil")
	}

	return s.cmd.Process.Pid, nil
}

// StdoutPipe returns a pipe that will be connected to the command's standard output.
// The pipe will continue to receive data until the process exits.
// Multiple calls to StdoutPipe will return independent readers.
func (s *Supervisor) StdoutPipe() (io.ReadCloser, error) {
	return s.stdoutMultiPipe.NewReader(), nil
}

// StderrPipe returns a pipe that will be connected to the command's standard error.
// The pipe will continue to receive data until the process exits.
// Multiple calls to StderrPipe will return independent readers.
func (s *Supervisor) StderrPipe() (io.ReadCloser, error) {
	return s.stderrMultiPipe.NewReader(), nil
}

// monitor handles the lifecycle of the supervised process
func (s *Supervisor) monitor() {
	defer func() {
		close(s.stoppedCh)
		// Close multipipes when process stops
		s.stdoutMultiPipe.Close()
		s.stderrMultiPipe.Close()
	}()

	// Channel to receive process exit
	exitCh := make(chan error, 1)
	go func() {
		err := s.cmd.Wait()
		// If process exited with an error, try to provide more context
		if err != nil {
			if exitErr, ok := err.(*exec.ExitError); ok {
				// Log the exit code for debugging
				if status, ok := exitErr.Sys().(syscall.WaitStatus); ok {
					s.logger.Error("Process exited with non-zero status",
						"exitCode", status.ExitStatus(),
						"signal", status.Signal(),
						"command", s.cmd.Path,
						"args", s.cmd.Args)

					// Exit code 127 typically means command not found
					if status.ExitStatus() == 127 {
						s.logger.Error("Exit code 127 usually means 'command not found'. Check that the command exists and is executable.")
					}
				}
			}
		}
		exitCh <- err
	}()

	// Main monitoring loop
	for {
		select {
		case sig := <-s.signalCh:
			// Forward signal to process
			if s.cmd.Process != nil {
				s.cmd.Process.Signal(sig)
			}

		case <-s.stopCh:
			// Graceful shutdown requested
			s.performGracefulShutdown(exitCh)
			return

		case err := <-exitCh:
			// Process exited on its own
			if err != nil {
				s.errorCh <- err
			}
			return
		}
	}
}

// performGracefulShutdown attempts graceful shutdown with SIGTERM, then SIGKILL
func (s *Supervisor) performGracefulShutdown(exitCh <-chan error) {
	if s.cmd.Process == nil {
		return
	}

	// Send SIGTERM to the entire process group (negative PID)
	syscall.Kill(-s.cmd.Process.Pid, syscall.SIGTERM)

	// Wait for graceful shutdown or timeout
	select {
	case err := <-exitCh:
		if err != nil {
			s.errorCh <- err
		}
		return

	case <-time.After(s.gracePeriod):
		// Grace period expired, force kill the entire process group
		syscall.Kill(-s.cmd.Process.Pid, syscall.SIGKILL)

		// Wait for process to exit
		select {
		case err := <-exitCh:
			if err != nil {
				s.errorCh <- fmt.Errorf("process killed after grace period: %w", err)
			}
		case <-time.After(time.Second):
			s.errorCh <- errors.New("process failed to exit after SIGKILL")
		}
	}
}
