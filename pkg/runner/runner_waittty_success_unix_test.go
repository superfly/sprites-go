//go:build unix && !windows

package runner

import (
	"bytes"
	"context"
	"os"
	"os/exec"
	"runtime"
	"strings"
	"sync"
	"testing"

	"syscall"

	creackpty "github.com/creack/pty"
)

// Test a happy-path WithWaitTTY using a stub PTY provider that the test allocates.
func TestTTY_WaitTTY_Success_StubPTY(t *testing.T) {
	t.Parallel()
	r := &Runner{}

	// Allocate a PTY pair
	master, slave, err := creackpty.Open()
	if err != nil {
		t.Fatalf("pty open: %v", err)
	}
	defer master.Close()
	// slave is closed in the WaitTTY callback after cmd.Start()

	cmd := exec.Command("sh", "-c", "echo hi; exit 3")
	cmd.Stdin = slave
	cmd.Stdout = slave
	cmd.Stderr = slave
	if cmd.SysProcAttr == nil {
		cmd.SysProcAttr = &syscall.SysProcAttr{}
	}
	cmd.SysProcAttr.Setsid = true
	cmd.SysProcAttr.Setctty = true

	var out bytes.Buffer
	code, runErr := r.RunContext(context.Background(), cmd,
		WithStdout(&out),
		WithWaitTTY(func(ctx context.Context) (*os.File, error) {
			// Ensure parent does not hold the slave after Start
			_ = slave.Close()
			return master, nil
		}),
	)
	if runErr != nil {
		t.Fatalf("run error: %v", runErr)
	}
	if code != 3 {
		t.Fatalf("exit code = %d", code)
	}
	norm := strings.ReplaceAll(out.String(), "\r\n", "\n")
	if strings.TrimSpace(norm) != "hi" {
		t.Fatalf("output = %q", out.String())
	}
}

// Stress the WaitTTY stub provider concurrently under GOMAXPROCS(1)
func TestTTY_WaitTTY_StubPTY_Concurrency_GOMAXPROCS1(t *testing.T) {
	old := runtime.GOMAXPROCS(1)
	defer runtime.GOMAXPROCS(old)

	r := &Runner{}
	const N = 64
	var wg sync.WaitGroup
	wg.Add(N)
	errs := make(chan error, N)

	for i := 0; i < N; i++ {
		go func() {
			defer wg.Done()
			master, slave, err := creackpty.Open()
			if err != nil {
				errs <- err
				return
			}
			defer master.Close()

			cmd := exec.Command("sh", "-c", "printf x; exit 0")
			cmd.Stdin = slave
			cmd.Stdout = slave
			cmd.Stderr = slave
			if cmd.SysProcAttr == nil {
				cmd.SysProcAttr = &syscall.SysProcAttr{}
			}
			cmd.SysProcAttr.Setsid = true
			cmd.SysProcAttr.Setctty = true

			var out bytes.Buffer
			code, err := r.Run(cmd, WithStdout(&out), WithWaitTTY(func(ctx context.Context) (*os.File, error) {
				_ = slave.Close()
				return master, nil
			}))
			if err != nil || code != 0 || out.String() != "x" {
				errs <- err
				return
			}
			errs <- nil
		}()
	}
	wg.Wait()
	close(errs)
	for e := range errs {
		if e != nil {
			t.Fatalf("concurrency error: %v", e)
		}
	}
}
