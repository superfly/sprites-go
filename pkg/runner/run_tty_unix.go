//go:build unix && !windows

package runner

import (
	"fmt"
	"io"
	"os"
	"syscall"

	creackpty "github.com/creack/pty"
)

// runWithTTY executes the command with a PTY. Output streams are merged and written to cfg.stdout.
// startTTYPlatform is used by Runner.startWithTTY to allocate PTY, start the process,
// wire IO pumpers, and signal readiness.
func (r *Runner) startTTYPlatform() error {
	var master *os.File
	var slave *os.File
	var err error

	var stderrPipe io.ReadCloser
	switch {
	case r.config.newTTY:
		master, slave, err = creackpty.Open()
		if err != nil {
			return fmt.Errorf("open pty: %w", err)
		}

		r.cmd.Stdin = slave
		r.cmd.Stdout = slave
		r.cmd.Stderr = slave
		if r.cmd.SysProcAttr == nil {
			r.cmd.SysProcAttr = &syscall.SysProcAttr{}
		}
		r.cmd.SysProcAttr.Setsid = true
		r.cmd.SysProcAttr.Setctty = true

		if err := r.cmd.Start(); err != nil {
			_ = master.Close()
			_ = slave.Close()
			return err
		}
		_ = slave.Close()
		r.pty = master
		close(r.ptyReady)

	case r.config.ttyMaster != nil:
		master = r.config.ttyMaster
		// If stderr capture is requested, prepare pipe before starting
		if r.config.stderr != nil {
			if p, perr := r.cmd.StderrPipe(); perr == nil {
				stderrPipe = p
			}
		}
		if err := r.cmd.Start(); err != nil {
			return err
		}
		r.pty = master
		close(r.ptyReady)

	case r.config.waitTTYFunc != nil:
		// If stderr capture is requested, prepare pipe before starting
		if r.config.stderr != nil {
			if p, perr := r.cmd.StderrPipe(); perr == nil {
				stderrPipe = p
			}
		}
		if err := r.cmd.Start(); err != nil {
			return err
		}
		// Obtain master asynchronously (e.g., via fd pass)
		m, werr := r.config.waitTTYFunc(r.ctx)
		if werr != nil {
			if r.cmd.Process != nil {
				_ = r.cmd.Process.Kill()
				_, _ = r.cmd.Process.Wait()
			}
			return werr
		}
		master = m
		r.pty = master
		close(r.ptyReady)

	default:
		return fmt.Errorf("tty mode not selected")
	}

	// Signal PID ready
	close(r.pidReady)

	// IO pumpers
	go func() {
		defer close(r.stdoutDone)
		_, _ = io.Copy(r.config.stdout, master)
	}()

	// If we have a stderr pipe (TTY modes where the child stderr is not bound to the PTY),
	// forward it to the configured stderr writer.
	if stderrPipe != nil && r.config.stderr != nil {
		go func() {
			defer close(r.stderrDone)
			_, _ = io.Copy(r.config.stderr, stderrPipe)
		}()
	} else {
		// No separate stderr stream; mark done
		close(r.stderrDone)
	}

	if r.config.stdin != nil {
		if r.config.consumeOnlyStdin {
			// For control-only stdin (e.g., resize messages), do not block Wait() on draining.
			// Close stdinDone immediately and drain in background.
			close(r.stdinDone)
			go func() {
				_, _ = io.Copy(io.Discard, r.config.stdin)
			}()
		} else {
			go func() {
				defer close(r.stdinDone)
				_, _ = io.Copy(master, r.config.stdin)
			}()
		}
	} else {
		close(r.stdinDone)
	}

	return nil
}
