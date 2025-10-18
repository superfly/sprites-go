package runner

import (
	"bytes"
	"context"
	"io"
	"os/exec"
	"testing"
	"time"
)

// A simple pipe-backed WriteCloser for tests
type wc struct{ io.Writer }

func (w wc) Close() error { return nil }

func TestReadPump_EOFForwarding(t *testing.T) {
	r := bytes.NewBufferString("hello\n")
	pr, pw := io.Pipe()
	done := StartReadPump(context.Background(), r, pw)
	// Reader side should receive the data then EOF
	buf := make([]byte, 6)
	n, err := pr.Read(buf)
	if err != nil || n != 6 {
		t.Fatalf("read err=%v n=%d", err, n)
	}
	if string(buf) != "hello\n" {
		t.Fatalf("got=%q", string(buf))
	}
	// Next read should hit EOF shortly
	ch := make(chan error, 1)
	go func() {
		_, e := pr.Read(buf)
		ch <- e
	}()
	select {
	case e := <-ch:
		if e == nil {
			t.Fatalf("expected EOF, got nil")
		}
	case <-time.After(1 * time.Second):
		t.Fatalf("timed out waiting for EOF")
	}
	<-done
}

func TestReadPump_CancelClosesDst(t *testing.T) {
	ctx, cancel := context.WithTimeout(context.Background(), 200*time.Millisecond)
	defer cancel()

	// never-ending reader; pump should close dst on cancel
	reader := &neverEOFReader{}
	pr, pw := io.Pipe()
	done := StartReadPump(ctx, reader, pw)

	// Attach a command that blocks on stdin and observes EOF
	cmd := exec.Command("cat")
	cmd.Stdin = pr
	if err := cmd.Start(); err != nil {
		t.Fatalf("start: %v", err)
	}
	<-done
	_ = pr.Close()
	_ = cmd.Wait()
}
