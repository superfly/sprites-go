package runner

import (
	"bytes"
	"context"
	"io"
	"os/exec"
	"runtime"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"
)

type slowWriter struct {
	delay  time.Duration
	buf    *bytes.Buffer
	writes int64
}

func (w *slowWriter) Write(p []byte) (int, error) {
	time.Sleep(w.delay)
	n, err := w.buf.Write(p)
	atomic.AddInt64(&w.writes, 1)
	return n, err
}

type chunkingWriter struct {
	buf   *bytes.Buffer
	chunk int
}

func (w *chunkingWriter) Write(p []byte) (int, error) {
	if w.chunk <= 0 {
		w.chunk = 1
	}
	written := 0
	for written < len(p) {
		n := w.chunk
		if n > len(p)-written {
			n = len(p) - written
		}
		if _, err := w.buf.Write(p[written : written+n]); err != nil {
			return written, err
		}
		written += n
	}
	return written, nil
}

// Non-TTY: cancel while stdin loop is active; ensure process is killed and we return.
func TestNonTTY_StdinCancel_KillsProcess(t *testing.T) {
	t.Parallel()
	r := &Runner{}

	// Use cat to block on stdin
	cmd := exec.Command("cat")
	var out bytes.Buffer
	ctx, cancel := context.WithTimeout(context.Background(), 500*time.Millisecond)
	defer cancel()

	// Provide a reader that does not finish within the timeout
	reader := io.MultiReader(strings.NewReader(strings.Repeat("x", 1<<20)), &neverEOFReader{})
	code, err := r.RunContext(ctx, cmd, WithStdout(&out), WithStderr(&out), WithStdin(reader))
	if err == nil && code == 0 {
		t.Fatalf("expected non-zero exit or error on cancel")
	}
}

type neverEOFReader struct{}

func (r *neverEOFReader) Read(p []byte) (int, error) {
	time.Sleep(10 * time.Millisecond)
	if len(p) == 0 {
		return 0, nil
	}
	p[0] = 'x'
	return 1, nil
}

// TTY: cancel while stdin copy is active; ensure process group is killed and we return.
func TestTTY_StdinCancel_KillsProcess(t *testing.T) {
	t.Parallel()
	r := &Runner{}
	cmd := exec.Command("cat")
	var out bytes.Buffer
	ctx, cancel := context.WithTimeout(context.Background(), 600*time.Millisecond)
	defer cancel()
	reader := &neverEOFReader{}
	code, err := r.RunContext(ctx, cmd, WithStdout(&out), WithNewTTY(), WithStdin(reader))
	if err == nil && code == 0 {
		t.Fatalf("expected non-zero exit or error on cancel (tty)")
	}
}

// Non-TTY: slow writers should not violate exit-after-drain ordering.
func TestNonTTY_SlowWriter_Ordering(t *testing.T) {
	t.Parallel()
	r := &Runner{}
	cmd := exec.Command("bash", "-c", "printf 'a%.0s' {1..8192}; printf 'b%.0s' {1..4096} 1>&2")
	var outBuf, errBuf bytes.Buffer
	swOut := &slowWriter{delay: 50 * time.Millisecond, buf: &outBuf}
	swErr := &slowWriter{delay: 50 * time.Millisecond, buf: &errBuf}
	start := time.Now()
	code, err := r.Run(cmd, WithStdout(swOut), WithStderr(swErr))
	elapsed := time.Since(start)
	if err != nil || code != 0 {
		t.Fatalf("err=%v code=%d", err, code)
	}
	if outBuf.Len() != 8192 || errBuf.Len() != 4096 {
		t.Fatalf("lens out=%d err=%d writesOut=%d writesErr=%d", outBuf.Len(), errBuf.Len(), atomic.LoadInt64(&swOut.writes), atomic.LoadInt64(&swErr.writes))
	}
	// Ensure elapsed time reflects total write calls and per-write delay
	totalWrites := atomic.LoadInt64(&swOut.writes) + atomic.LoadInt64(&swErr.writes)
	expectedMin := time.Duration(totalWrites) * (1 * time.Millisecond)
	if elapsed < expectedMin {
		t.Fatalf("elapsed too short: got=%v want>=%v (writes=%d)", elapsed, expectedMin, totalWrites)
	}
}

// TTY: slow writer on merged stream.
func TestTTY_SlowWriter_Ordering(t *testing.T) {
	t.Parallel()
	r := &Runner{}
	cmd := exec.Command("sh", "-c", "echo one; echo two 1>&2")
	var out bytes.Buffer
	sw := &slowWriter{delay: 2 * time.Millisecond, buf: &out}
	code, err := r.Run(cmd, WithStdout(sw), WithNewTTY())
	if err != nil || code != 0 {
		t.Fatalf("err=%v code=%d", err, code)
	}
	norm := strings.ReplaceAll(out.String(), "\r\n", "\n")
	if strings.TrimSpace(norm) != "one\ntwo" {
		t.Fatalf("got=%q", out.String())
	}
}

// Non-TTY: verify short writer behavior doesn't drop bytes overall under stress.
func TestNonTTY_ShortWriter_Stress_GOMAXPROCS1(t *testing.T) {
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
			// Use dd for deterministic sizes and portability
			sh := "dd if=/dev/zero bs=1 count=32768 2>/dev/null; dd if=/dev/zero bs=1 count=16384 1>&2 2>/dev/null"
			cmd := exec.Command("sh", "-c", sh)
			var outB, errB bytes.Buffer
			swOut := &chunkingWriter{buf: &outB, chunk: 7}
			swErr := &chunkingWriter{buf: &errB, chunk: 5}
			code, err := r.Run(cmd, WithStdout(swOut), WithStderr(swErr))
			if err != nil || code != 0 {
				errs <- err
				return
			}
			if outB.Len() != 32768 || errB.Len() != 16384 {
				errs <- io.ErrShortWrite
				return
			}
			errs <- nil
		}()
	}
	wg.Wait()
	close(errs)
	for e := range errs {
		if e != nil {
			t.Fatalf("error: %v", e)
		}
	}
}
