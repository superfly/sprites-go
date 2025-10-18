package runner

import (
	"bytes"
	"context"
	"fmt"
	"os/exec"
	"runtime"
	"testing"
	"time"
)

func TestNonTTY_LargeOutput_STDOUT_STDERR(t *testing.T) {
	t.Parallel()
	r := &Runner{}

	// 2MB stdout, 1MB stderr using dd from /dev/zero (silence dd progress to stderr)
	// Important: redirect order so stdout duplicates to current stderr BEFORE silencing stderr
	sh := "dd if=/dev/zero bs=1024 count=2048 2>/dev/null; dd if=/dev/zero bs=1024 count=1024 1>&2 2>/dev/null"
	cmd := exec.Command("sh", "-c", sh)
	var out, errb bytes.Buffer
	code, err := r.RunContext(context.Background(), cmd, WithStdout(&out), WithStderr(&errb))
	if err != nil {
		t.Fatalf("run error: %v", err)
	}
	if code != 0 {
		t.Fatalf("exit: %d", code)
	}
	if out.Len() != 2048*1024 {
		t.Fatalf("stdout len = %d", out.Len())
	}
	if errb.Len() != 1024*1024 {
		t.Fatalf("stderr len = %d", errb.Len())
	}
}

func TestTTY_LargeOutput_AndOrdering(t *testing.T) {
	t.Parallel()
	r := &Runner{}

	// 256KB followed by marker, ensure exact length and marker at end
	sh := "dd if=/dev/zero bs=1024 count=256 2>/dev/null; printf END"
	cmd := exec.Command("sh", "-c", sh)
	var out bytes.Buffer
	code, err := r.RunContext(context.Background(), cmd, WithStdout(&out), WithNewTTY())
	if err != nil {
		t.Fatalf("run error: %v", err)
	}
	if code != 0 {
		t.Fatalf("exit: %d", code)
	}
	// normalize CRLF
	data := bytes.ReplaceAll(out.Bytes(), []byte("\r\n"), []byte("\n"))
	if len(data) < 256*1024+3 {
		t.Fatalf("merged len too small: %d", len(data))
	}
	if !bytes.HasSuffix(data, []byte("END")) {
		t.Fatalf("missing END suffix")
	}
}

func TestNonTTY_Concurrency_Large_GOMAXPROCS1(t *testing.T) {
	old := runtime.GOMAXPROCS(1)
	defer runtime.GOMAXPROCS(old)
	r := &Runner{}

	ctx, cancel := context.WithTimeout(context.Background(), 15*time.Second)
	defer cancel()

	const N = 80
	errs := make(chan error, N)
	done := make(chan struct{})
	for i := 0; i < N; i++ {
		go func() {
			sh := "dd if=/dev/zero bs=1024 count=128 2>/dev/null; dd if=/dev/zero bs=1024 count=64 1>&2 2>/dev/null"
			cmd := exec.CommandContext(ctx, "sh", "-c", sh)
			var out, errb bytes.Buffer
			code, err := r.Run(cmd, WithStdout(&out), WithStderr(&errb))
			if err != nil || code != 0 || out.Len() != 128*1024 || errb.Len() != 64*1024 {
				errs <- fmt.Errorf("err=%v code=%d out=%d err=%d", err, code, out.Len(), errb.Len())
				return
			}
			errs <- nil
		}()
	}
	go func() {
		ok := true
		for i := 0; i < N; i++ {
			if e := <-errs; e != nil {
				ok = false
			}
		}
		if ok {
			close(done)
		}
	}()
	select {
	case <-done:
	case <-ctx.Done():
		t.Fatal("timeout waiting for large concurrency")
	}
}
