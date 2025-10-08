package terminal

import (
	"bytes"
	"io"
	"net/http"
	"net/http/httptest"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// blockingStdinReader simulates real stdin that blocks forever
type blockingStdinReader struct {
	mu        sync.Mutex
	unblocked bool
	ch        chan []byte
}

func newBlockingStdinReader() *blockingStdinReader {
	return &blockingStdinReader{
		ch: make(chan []byte),
	}
}

func (r *blockingStdinReader) Read(p []byte) (int, error) {
	r.mu.Lock()
	if r.unblocked {
		r.mu.Unlock()
		return 0, io.EOF
	}
	r.mu.Unlock()

	// Block until we get data or are unblocked
	data := <-r.ch
	n := copy(p, data)
	return n, nil
}

func (r *blockingStdinReader) unblock() {
	r.mu.Lock()
	r.unblocked = true
	r.mu.Unlock()
	close(r.ch)
}

// TestWebSocketTTYExitWithBlockingStdin verifies that TTY mode properly exits
// even when stdin is attached and blocking. This test would hang indefinitely
// without the adapter.Close() fix.
func TestWebSocketTTYExitWithBlockingStdin(t *testing.T) {
	// Create a quick-exiting command so we don't actually need input
	session := NewSession(
		WithCommand("echo", "test complete"),
		WithTTY(true),
	)

	handler := NewWebSocketHandler(session)
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if err := handler.Handle(w, r); err != nil {
			t.Logf("handler error (may be normal): %v", err)
		}
	}))
	defer server.Close()

	wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
	req, err := http.NewRequest("GET", wsURL, nil)
	require.NoError(t, err)

	cmd := Command(req, "tty-blocking-stdin")

	// Create a blocking stdin reader that will never provide data
	blockingReader := newBlockingStdinReader()
	defer blockingReader.unblock() // Ensure cleanup

	cmd.Stdin = blockingReader
	cmd.Tty = true

	var stdout bytes.Buffer
	cmd.Stdout = &stdout

	// Run with timeout to catch hangs
	done := make(chan error, 1)
	go func() {
		done <- cmd.Run()
	}()

	select {
	case err := <-done:
		// The test passes if we complete without hanging
		// The command should exit normally even though stdin is blocking
		if err != nil {
			t.Logf("Command completed with error (may be normal for websocket close): %v", err)
		}
		// Verify we got output
		output := stdout.String()
		if !strings.Contains(output, "test complete") {
			t.Errorf("Expected 'test complete' in output, got: %q", output)
		}
		t.Log("Successfully completed without hanging on blocking stdin")
	case <-time.After(5 * time.Second):
		t.Fatal("Test hung - stdin goroutine blocked and adapter.Close() did not unblock it")
	}
}

// TestWebSocketTTYInteractiveExit tests a more realistic scenario where
// the user types "exit" in an interactive shell
func TestWebSocketTTYInteractiveExit(t *testing.T) {
	// Create an interactive shell session
	session := NewSession(
		WithCommand("sh", "-c", "echo 'Type exit:'; read cmd; echo \"You typed: $cmd\""),
		WithTTY(true),
	)

	handler := NewWebSocketHandler(session)
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if err := handler.Handle(w, r); err != nil {
			t.Errorf("handler error: %v", err)
		}
	}))
	defer server.Close()

	wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
	req, err := http.NewRequest("GET", wsURL, nil)
	require.NoError(t, err)

	cmd := Command(req, "tty-interactive")

	// Simulate user typing "exit"
	cmd.Stdin = strings.NewReader("exit\n")
	cmd.Tty = true

	var stdout bytes.Buffer
	cmd.Stdout = &stdout

	// This should complete after processing the input
	err = cmd.Run()
	assert.NoError(t, err)

	// Verify the interaction
	output := stdout.String()
	assert.Contains(t, output, "Type exit:")
	assert.Contains(t, output, "You typed: exit")
}

// TestWebSocketTTYNoStdin verifies that TTY mode works without stdin
func TestWebSocketTTYNoStdin(t *testing.T) {
	session := NewSession(
		WithCommand("echo", "no stdin needed"),
		WithTTY(true),
	)

	handler := NewWebSocketHandler(session)
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if err := handler.Handle(w, r); err != nil {
			t.Errorf("handler error: %v", err)
		}
	}))
	defer server.Close()

	wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
	req, err := http.NewRequest("GET", wsURL, nil)
	require.NoError(t, err)

	cmd := Command(req, "tty-no-stdin")

	// No stdin set - this is how the original test worked
	cmd.Stdin = nil
	cmd.Tty = true

	var stdout bytes.Buffer
	cmd.Stdout = &stdout

	err = cmd.Run()
	assert.NoError(t, err)
	assert.Contains(t, stdout.String(), "no stdin needed")
}
