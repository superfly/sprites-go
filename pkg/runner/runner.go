package runner

import (
	"context"
	"errors"
	"io"
	"os"
	"os/exec"
	"sync"
	"syscall"

	"golang.org/x/sys/unix"
)

// Runner runs commands with strict IO/PTY semantics.
//
// New async API (preferred by server handlers):
//
//	r := NewWithContext(ctx, cmd, opts...)
//	_ = r.Run()        // starts immediately, returns only Start error
//	pid := r.PID()     // blocks until PID is available
//	_ = r.Wait()       // waits for process and IO to drain
//	code := r.ExitCode()
//
// Legacy synchronous API is preserved via Run/RunContext free functions below.
type Runner struct {
	// immutable after construction
	cmd    *exec.Cmd
	config *runConfig

	// lifecycle
	ctx    context.Context
	cancel context.CancelFunc

	// pid readiness (closed right after successful Start)
	pidReady chan struct{}

	// PTY state (for TTY mode resize)
	pty      *os.File
	ptyReady chan struct{}

	// IO goroutine completion signals
	stdinDone  chan struct{}
	stdoutDone chan struct{}
	stderrDone chan struct{}

	// exit state
	mu       sync.Mutex
	exitCode int
	waited   bool
}

// Option configures a run.
type Option func(*runConfig)

type runConfig struct {
	stdin  io.Reader
	stdout io.Writer
	stderr io.Writer

	// TTY options (mutually exclusive)
	newTTY      bool
	ttyMaster   *os.File
	waitTTYFunc func(ctx context.Context) (*os.File, error)

	// When true in TTY mode, consume stdin reader but discard bytes (for control-only paths)
	consumeOnlyStdin bool
}

// WithStdin sets the stdin source to copy into the command (or PTY) until EOF/cancel.
func WithStdin(r io.Reader) Option {
	return func(rc *runConfig) { rc.stdin = r }
}

// WithStdout sets the destination for stdout (or merged PTY stream).
func WithStdout(w io.Writer) Option {
	return func(rc *runConfig) { rc.stdout = w }
}

// WithStderr sets the destination for stderr (non-TTY only).
func WithStderr(w io.Writer) Option {
	return func(rc *runConfig) { rc.stderr = w }
}

// WithNewTTY allocates a new PTY and wires the child to its slave; merged output to stdout.
func WithNewTTY() Option {
	return func(rc *runConfig) { rc.newTTY = true }
}

// WithTTY uses a caller-provided PTY master; assumes the child is wired to the slave externally.
func WithTTY(tty *os.File) Option {
	return func(rc *runConfig) { rc.ttyMaster = tty }
}

// WithWaitTTY provides a callback that returns a PTY master after the command starts.
// The library does not care how the PTY master is obtained (e.g., fd pass via a socket).
func WithWaitTTY(fn func(ctx context.Context) (*os.File, error)) Option {
	return func(rc *runConfig) { rc.waitTTYFunc = fn }
}

// WithConsumeOnlyStdin causes the runner to read from stdin but discard the bytes
// (useful in TTY mode to process control messages without sending data to the process).
func WithConsumeOnlyStdin() Option {
	return func(rc *runConfig) { rc.consumeOnlyStdin = true }
}

// New creates a Runner with Background context.
func New(cmd *exec.Cmd, opts ...Option) (*Runner, error) {
	return NewWithContext(context.Background(), cmd, opts...)
}

// NewWithContext creates a Runner bound to ctx.
func NewWithContext(ctx context.Context, cmd *exec.Cmd, opts ...Option) (*Runner, error) {
	cfg := &runConfig{}
	for _, o := range opts {
		o(cfg)
	}
	if err := validateOptions(cfg); err != nil {
		return nil, err
	}
	rctx, cancel := context.WithCancel(ctx)
	return &Runner{
		cmd:        cmd,
		config:     cfg,
		ctx:        rctx,
		cancel:     cancel,
		pidReady:   make(chan struct{}),
		ptyReady:   make(chan struct{}),
		stdinDone:  make(chan struct{}),
		stdoutDone: make(chan struct{}),
		stderrDone: make(chan struct{}),
		exitCode:   -1,
	}, nil
}

// PID blocks until the PID is available and returns it. Returns -1 if not started.
func (r *Runner) PID() int {
	<-r.pidReady
	if r.cmd == nil || r.cmd.Process == nil {
		return -1
	}
	return r.cmd.Process.Pid
}

// ExitCode returns the stored exit code. Valid after Wait().
func (r *Runner) ExitCode() int {
	r.mu.Lock()
	defer r.mu.Unlock()
	return r.exitCode
}

// RunContext is a compatibility helper that executes the given command with options
// using the newer async Runner under the hood, returning the exit code and any
// non-exit-related error.
func (r *Runner) RunContext(ctx context.Context, cmd *exec.Cmd, opts ...Option) (int, error) {
	rr, err := NewWithContext(ctx, cmd, opts...)
	if err != nil {
		return -1, err
	}
	if err := rr.Start(); err != nil {
		return -1, err
	}
	if err := rr.Wait(); err != nil {
		return -1, err
	}
	return rr.ExitCode(), nil
}

// Run is like RunContext with Background context.
func (r *Runner) Run(cmd *exec.Cmd, opts ...Option) (int, error) {
	return r.RunContext(context.Background(), cmd, opts...)
}

// Start starts the process and returns immediately on success.
// It returns an error only if cmd.Start() fails.
func (r *Runner) Start() error {
	if r.config.newTTY || r.config.ttyMaster != nil || r.config.waitTTYFunc != nil {
		return r.startWithTTY()
	}
	return r.startWithoutTTY()
}

// Wait blocks until the process exits and IO drains, storing the exit code.
func (r *Runner) Wait() error {
	// Wait for process to exit
	waitCh := make(chan error, 1)
	go func() { waitCh <- r.cmd.Wait() }()

	var waitErr error
	select {
	case <-r.ctx.Done():
		// Kill the process group
		if r.cmd.Process != nil {
			if pgid, err := syscall.Getpgid(r.cmd.Process.Pid); err == nil {
				_ = syscall.Kill(-pgid, syscall.SIGKILL)
			} else {
				_ = r.cmd.Process.Kill()
			}
		}
		waitErr = <-waitCh
	case waitErr = <-waitCh:
	}

	// Drain IO goroutines (stdin is not required to drain; only stdout/stderr)
	<-r.stdoutDone
	<-r.stderrDone

	// Store exit code
	r.mu.Lock()
	defer r.mu.Unlock()
	r.waited = true
	if waitErr != nil {
		if ee, ok := waitErr.(*exec.ExitError); ok {
			r.exitCode = ee.ExitCode()
			return nil
		}
		r.exitCode = -1
		return waitErr
	}
	r.exitCode = 0
	return nil
}

// Resize resizes the PTY (TTY mode only).
func (r *Runner) Resize(cols, rows uint16) error {
	// If not in TTY mode, return immediately with an error instead of blocking
	if !r.config.newTTY && r.config.ttyMaster == nil && r.config.waitTTYFunc == nil {
		return errors.New("no PTY allocated")
	}
	// If ptyReady is nil, PTY was allocated synchronously (WithNewTTY). Otherwise wait for it.
	if r.ptyReady != nil {
		select {
		case <-r.ptyReady:
		default:
			<-r.ptyReady
		}
	}
	if r.pty == nil {
		return errors.New("no PTY allocated")
	}
	ws := &unix.Winsize{Row: rows, Col: cols}
	if err := unix.IoctlSetWinsize(int(r.pty.Fd()), unix.TIOCSWINSZ, ws); err != nil {
		return err
	}
	// Best-effort: also notify the foreground process group with SIGWINCH.
	// This can be necessary in some environments (e.g., containerized slaves)
	// even though TIOCSWINSZ should normally generate SIGWINCH.
	if pgid, err := unix.IoctlGetInt(int(r.pty.Fd()), unix.TIOCGPGRP); err == nil && pgid > 0 {
		_ = syscall.Kill(-pgid, syscall.SIGWINCH)
	}
	return nil
}

// startWithoutTTY starts the process in non-TTY mode and launches stdin copier if needed.
func (r *Runner) startWithoutTTY() error {
	// Direct writers to avoid extra buffering layers
	r.cmd.Stdout = r.config.stdout
	r.cmd.Stderr = r.config.stderr

	if r.cmd.SysProcAttr == nil {
		r.cmd.SysProcAttr = &syscall.SysProcAttr{}
	}
	r.cmd.SysProcAttr.Setpgid = true

	// Stdin pipe if provided
	var stdinPipe io.WriteCloser
	if r.config.stdin != nil {
		p, err := r.cmd.StdinPipe()
		if err != nil {
			return err
		}
		stdinPipe = p
	} else {
		r.cmd.Stdin = nil
	}

	if err := r.cmd.Start(); err != nil {
		if stdinPipe != nil {
			_ = stdinPipe.Close()
		}
		return err
	}

	// Signal PID ready
	close(r.pidReady)

	// Stdin copier: do not block Wait() on stdin draining
	if stdinPipe != nil {
		// Close stdinDone immediately and drain in background
		close(r.stdinDone)
		go func() {
			_, _ = io.Copy(stdinPipe, r.config.stdin)
			_ = stdinPipe.Close()
		}()
	} else {
		close(r.stdinDone)
	}

	// No separate stdout/stderr goroutines in non-TTY mode (process writes directly)
	close(r.stdoutDone)
	close(r.stderrDone)
	return nil
}

// startWithTTY starts the process in TTY mode and launches IO pumpers.
func (r *Runner) startWithTTY() error {
	return r.startTTYPlatform()
}

var (
	errMissingStdout  = errors.New("stdout writer is required")
	errMissingStderr  = errors.New("stderr writer is required in non-TTY mode")
	errConflictingTTY = errors.New("conflicting TTY options")
)

func validateOptions(cfg *runConfig) error {
	if cfg.stdout == nil {
		return errMissingStdout
	}
	// Conflicts between TTY options
	ttyCount := 0
	if cfg.newTTY {
		ttyCount++
	}
	if cfg.ttyMaster != nil {
		ttyCount++
	}
	if cfg.waitTTYFunc != nil {
		ttyCount++
	}
	if ttyCount > 1 {
		return errConflictingTTY
	}
	if ttyCount == 0 {
		// Non-TTY requires separate stderr
		if cfg.stderr == nil {
			return errMissingStderr
		}
		return nil
	}
	// In TTY mode, we allow an optional stderr writer (used for capturing process stderr
	// such as tmux stderr that is not routed through the PTY). If provided, start code
	// will attempt to attach a pipe for stderr when possible.
	return nil
}
