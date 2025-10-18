package runner

import (
	"bytes"
	"context"
	"os/exec"
	"runtime"
	"strings"
	"sync"
	"testing"
	"time"
)

func TestNonTTY_EchoStdoutStderr(t *testing.T) {
	t.Parallel()
	r := &Runner{}

	cmd := exec.Command("sh", "-c", "echo out; echo err 1>&2")
	var outBuf, errBuf bytes.Buffer
	code, err := r.RunContext(context.Background(), cmd,
		WithStdout(&outBuf),
		WithStderr(&errBuf),
	)
	if err != nil {
		t.Fatalf("run error: %v", err)
	}
	if code != 0 {
		t.Fatalf("exit code: %d", code)
	}
	if strings.TrimSpace(outBuf.String()) != "out" {
		t.Fatalf("stdout mismatch: %q", outBuf.String())
	}
	if strings.TrimSpace(errBuf.String()) != "err" {
		t.Fatalf("stderr mismatch: %q", errBuf.String())
	}
}

func TestNonTTY_StdinLoop(t *testing.T) {
	t.Parallel()
	r := &Runner{}

	cmd := exec.Command("cat")
	var outBuf bytes.Buffer
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()

	code, err := r.RunContext(ctx, cmd,
		WithStdout(&outBuf),
		WithStderr(&outBuf),
		WithStdin(strings.NewReader("hello\n")),
	)
	if err != nil {
		t.Fatalf("run error: %v", err)
	}
	if code != 0 {
		t.Fatalf("exit code: %d", code)
	}
	if strings.TrimSpace(outBuf.String()) != "hello" {
		t.Fatalf("roundtrip mismatch: %q", outBuf.String())
	}
}

func TestNonTTY_Concurrency_GOMAXPROCS1(t *testing.T) {
	// Force 1 P for this test to surface scheduling races
	old := runtime.GOMAXPROCS(1)
	defer runtime.GOMAXPROCS(old)

	r := &Runner{}
	const N = 200
	var wg sync.WaitGroup
	wg.Add(N)

	errs := make(chan error, N)

	for i := 0; i < N; i++ {
		go func() {
			defer wg.Done()
			cmd := exec.Command("sh", "-c", "printf %02048d; printf %02048d 1>&2")
			var outBuf, errBuf bytes.Buffer
			code, err := r.Run(cmd, WithStdout(&outBuf), WithStderr(&errBuf))
			if err != nil {
				errs <- err
				return
			}
			if code != 0 {
				errs <- err
				return
			}
			if outBuf.Len() != 2048 || errBuf.Len() != 2048 {
				errs <- err
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
