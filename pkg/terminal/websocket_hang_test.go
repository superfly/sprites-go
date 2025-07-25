package terminal

import (
	"bytes"
	"io"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// infiniteStdinReader simulates a real terminal stdin that blocks forever
type infiniteStdinReader struct{}

func (r *infiniteStdinReader) Read(p []byte) (int, error) {
	// Block forever - simulates a real terminal where stdin is always available
	select {}
}

// TestWebSocketTTYBashExitHang reproduces the issue where sprite exec -tty /bin/bash
// hangs after exiting the bash process
func TestWebSocketTTYBashExitHang(t *testing.T) {
	// Create a session that simulates bash exiting immediately
	session := NewSession(
		WithCommand("sh", "-c", "echo 'bash-4.2$ '; sleep 0.1; echo 'exit'"),
		WithTTY(true),
	)

	handler := NewWebSocketHandler(session)
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		t.Log("Server: handling request")
		if err := handler.Handle(w, r); err != nil {
			t.Errorf("handler error: %v", err)
		}
		t.Log("Server: handler returned")
	}))
	defer server.Close()

	wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
	req, err := http.NewRequest("GET", wsURL, nil)
	require.NoError(t, err)

	cmd := Command(req, "tty-bash-exit")

	// Use an infinite stdin reader to simulate a real terminal
	cmd.Stdin = &infiniteStdinReader{}
	cmd.Tty = true

	var stdout bytes.Buffer
	cmd.Stdout = &stdout

	// Start the command in a goroutine
	done := make(chan error, 1)
	go func() {
		t.Log("Client: calling Run()")
		err := cmd.Run()
		t.Log("Client: Run() returned with error:", err)
		done <- err
	}()

	// The command should complete within 2 seconds
	select {
	case err := <-done:
		// Good - command completed
		assert.NoError(t, err)
		output := stdout.String()
		assert.Contains(t, output, "bash-4.2$ ")
		assert.Contains(t, output, "exit")
	case <-time.After(2 * time.Second):
		// Bad - command is hanging
		t.Log("Client state - IsDone:", cmd.IsDone(), "ExitCode:", cmd.ExitCode())
		t.Fatal("Command hung after bash exited - this reproduces the reported issue")
	}
}

// TestWebSocketTTYWithPipeStdin tests that TTY mode works correctly with pipe stdin
func TestWebSocketTTYWithPipeStdin(t *testing.T) {
	// Create a session that reads one line and exits
	session := NewSession(
		WithCommand("sh", "-c", "read line; echo \"Got: $line\""),
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

	cmd := Command(req, "tty-pipe-stdin")

	// Use a pipe for stdin
	stdinReader, stdinWriter := io.Pipe()
	cmd.Stdin = stdinReader
	cmd.Tty = true

	var stdout bytes.Buffer
	cmd.Stdout = &stdout

	// Start the command in a goroutine
	done := make(chan error, 1)
	go func() {
		done <- cmd.Run()
	}()

	// Send input and close stdin
	stdinWriter.Write([]byte("hello\n"))
	stdinWriter.Close()

	// The command should complete
	select {
	case err := <-done:
		assert.NoError(t, err)
		assert.Contains(t, stdout.String(), "Got: hello")
	case <-time.After(2 * time.Second):
		t.Fatal("Command hung with pipe stdin")
	}
}
