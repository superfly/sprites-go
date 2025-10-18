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
	"time"
)

func TestTTY_BasicMergedOutput(t *testing.T) {
	t.Parallel()
	r := &Runner{}

	cmd := exec.Command("sh", "-c", "echo out; echo err 1>&2; exit 7")
	var out bytes.Buffer
	code, err := r.RunContext(context.Background(), cmd,
		WithStdout(&out),
		WithNewTTY(),
	)
	if err != nil {
		t.Fatalf("run error: %v", err)
	}
	if code != 7 {
		t.Fatalf("exit code: %d", code)
	}
	// PTY adds CRLF; normalize to LF for comparison
	normalized := strings.ReplaceAll(out.String(), "\r\n", "\n")
	got := strings.Split(strings.TrimSpace(normalized), "\n")
	if len(got) != 2 || got[0] != "out" || got[1] != "err" {
		t.Fatalf("merged output bad: %q", out.String())
	}
}

func TestTTY_WaitTTY_Callback(t *testing.T) {
	t.Parallel()
	r := &Runner{}

	cmd := exec.Command("sh", "-c", "echo hello")
	var out bytes.Buffer

	// Fake a delayed PTY master provider: here we simply return an error to ensure cleanup
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()

	_, err := r.RunContext(ctx, cmd,
		WithStdout(&out),
		WithWaitTTY(func(ctx context.Context) (*os.File, error) {
			// In real world we would block on a console socket and receive an fd
			return nil, context.Canceled
		}),
	)
	if err == nil {
		t.Fatalf("expected error from WaitTTY provider")
	}
}

func TestTTY_Concurrency_GOMAXPROCS1(t *testing.T) {
	old := runtime.GOMAXPROCS(1)
	defer runtime.GOMAXPROCS(old)

	r := &Runner{}
	const N = 100
	var wg sync.WaitGroup
	wg.Add(N)
	errs := make(chan error, N)

	for i := 0; i < N; i++ {
		go func() {
			defer wg.Done()
			cmd := exec.Command("sh", "-c", "printf foo; printf bar 1>&2")
			var out bytes.Buffer
			code, err := r.Run(cmd, WithStdout(&out), WithNewTTY())
			if err != nil || code != 0 {
				errs <- err
				return
			}
			if out.String() != "foobar" {
				errs <- context.DeadlineExceeded
				return
			}
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
