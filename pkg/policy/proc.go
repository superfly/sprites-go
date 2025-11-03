package policy

import (
	"bufio"
	"context"
	"fmt"
	"io"
	"os/exec"
	"syscall"
	"time"

	"github.com/superfly/sprite-env/pkg/tap"
)

// managedProcess wraps an external process with logging and control.
type managedProcess struct {
	cmd  *exec.Cmd
	name string
}

func startProcess(ctx context.Context, name string, args ...string) (*managedProcess, error) {
	logger := tap.Logger(ctx).With("component", "policy", "proc", name)
	cmd := exec.Command(args[0], args[1:]...)

	stdout, err := cmd.StdoutPipe()
	if err != nil {
		return nil, fmt.Errorf("stdout pipe: %w", err)
	}
	stderr, err := cmd.StderrPipe()
	if err != nil {
		return nil, fmt.Errorf("stderr pipe: %w", err)
	}

	if err := cmd.Start(); err != nil {
		return nil, fmt.Errorf("start %s: %w", name, err)
	}

	go streamLines(logger, stdout, false)
	go streamLines(logger, stderr, true)

	return &managedProcess{cmd: cmd, name: name}, nil
}

func (p *managedProcess) Reload(ctx context.Context) error {
	if p == nil || p.cmd == nil || p.cmd.Process == nil {
		return nil
	}
	return p.cmd.Process.Signal(syscall.SIGHUP)
}

func (p *managedProcess) Stop(ctx context.Context) error {
	if p == nil || p.cmd == nil || p.cmd.Process == nil {
		return nil
	}
	_ = p.cmd.Process.Signal(syscall.SIGTERM)
	done := make(chan error, 1)
	go func() { done <- p.cmd.Wait() }()
	select {
	case <-time.After(3 * time.Second):
		_ = p.cmd.Process.Kill()
		<-done
	case <-ctx.Done():
		return ctx.Err()
	case <-done:
	}
	return nil
}

func streamLines(logger any, r io.Reader, isErr bool) {
	l, ok := logger.(interface {
		Info(string, ...any)
		Warn(string, ...any)
	})
	if !ok {
		return
	}
	scanner := bufio.NewScanner(r)
	scanner.Buffer(make([]byte, 0, 64*1024), 1024*1024)
	for scanner.Scan() {
		txt := scanner.Text()
		if isErr {
			l.Warn(txt)
		} else {
			l.Info(txt)
		}
	}
}
