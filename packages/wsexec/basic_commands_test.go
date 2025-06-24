package wsexec_test

import (
	"bytes"
	"context"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
	"time"

	"github.com/sprite-env/packages/wsexec"
)

// TestBasicEchoCommand tests basic command execution without TTY
func TestBasicEchoCommand(t *testing.T) {
	// Create test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		// Create server command
		cmd := &wsexec.ServerCommand{
			Path: "echo",
			Args: []string{"echo", "hello", "world"},
		}

		// Handle the request
		if err := cmd.Handle(w, r); err != nil {
			t.Errorf("Server handle error: %v", err)
		}
	}))
	defer server.Close()

	// Create client request
	req, err := http.NewRequest("GET", server.URL+"/exec/test/websocket", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}

	// Update scheme for WebSocket
	req.URL.Scheme = "ws"

	// Execute command
	var stdout bytes.Buffer
	cmd := wsexec.Command(req, "echo", "hello", "world")
	cmd.Stdout = &stdout
	cmd.PingInterval = 100 * time.Millisecond

	if err := cmd.Run(); err != nil {
		t.Fatalf("Command failed: %v", err)
	}

	// Check output
	output := strings.TrimSpace(stdout.String())
	if output != "hello world" {
		t.Errorf("Expected 'hello world', got %q", output)
	}

	// Check exit code
	if code := cmd.ExitCode(); code != 0 {
		t.Errorf("Expected exit code 0, got %d", code)
	}
}

// TestStdinPipeWithCat tests stdin/stdout interaction using cat
func TestStdinPipeWithCat(t *testing.T) {
	// Create test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := &wsexec.ServerCommand{
			Path: "cat",
			Args: []string{"cat"},
		}

		if err := cmd.Handle(w, r); err != nil {
			t.Errorf("Server handle error: %v", err)
		}
	}))
	defer server.Close()

	// Create client
	req, err := http.NewRequest("GET", server.URL+"/exec/test/websocket", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}
	req.URL.Scheme = "ws"

	// Set up I/O
	stdin := strings.NewReader("test input\nanother line\n")
	var stdout bytes.Buffer

	cmd := wsexec.Command(req, "cat")
	cmd.Stdin = stdin
	cmd.Stdout = &stdout
	cmd.PingInterval = 100 * time.Millisecond

	if err := cmd.Run(); err != nil {
		t.Fatalf("Command failed: %v", err)
	}

	// Check output
	if stdout.String() != "test input\nanother line\n" {
		t.Errorf("Expected 'test input\\nanother line\\n', got %q", stdout.String())
	}
}

// TestStderrCapture tests stderr handling
func TestStderrCapture(t *testing.T) {
	// Create test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := &wsexec.ServerCommand{
			Path: "sh",
			Args: []string{"sh", "-c", "echo stdout; echo stderr >&2"},
		}

		if err := cmd.Handle(w, r); err != nil {
			t.Errorf("Server handle error: %v", err)
		}
	}))
	defer server.Close()

	// Create client
	req, err := http.NewRequest("GET", server.URL+"/exec/test/websocket", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}
	req.URL.Scheme = "ws"

	var stdout, stderr bytes.Buffer
	cmd := wsexec.Command(req, "sh", "-c", "echo stdout; echo stderr >&2")
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr
	cmd.PingInterval = 100 * time.Millisecond

	if err := cmd.Run(); err != nil {
		t.Fatalf("Command failed: %v", err)
	}

	// Check outputs
	if strings.TrimSpace(stdout.String()) != "stdout" {
		t.Errorf("Expected 'stdout' on stdout, got %q", stdout.String())
	}
	if strings.TrimSpace(stderr.String()) != "stderr" {
		t.Errorf("Expected 'stderr' on stderr, got %q", stderr.String())
	}
}

// TestCommandContextCancellation tests command cancellation with context
func TestCommandContextCancellation(t *testing.T) {
	// Create test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := &wsexec.ServerCommand{
			Path: "sleep",
			Args: []string{"sleep", "10"},
		}

		if err := cmd.Handle(w, r); err != nil {
			// Expected to be cancelled
			t.Logf("Server handle error (expected): %v", err)
		}
	}))
	defer server.Close()

	// Create client with timeout
	ctx, cancel := context.WithTimeout(context.Background(), 200*time.Millisecond)
	defer cancel()

	req, err := http.NewRequest("GET", server.URL+"/exec/test/websocket", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}
	req.URL.Scheme = "ws"

	cmd := wsexec.CommandContext(ctx, req, "sleep", "10")
	cmd.PingInterval = 50 * time.Millisecond

	start := time.Now()
	err = cmd.Run()
	duration := time.Since(start)

	// Should timeout
	if err == nil {
		t.Error("Expected timeout error")
	}
	if !strings.Contains(err.Error(), "context") {
		t.Errorf("Expected context error, got: %v", err)
	}

	// Should take around 200ms, not 10s
	if duration > 1*time.Second {
		t.Errorf("Command took too long: %v", duration)
	}
}

// TestNonZeroExitCode tests handling of non-zero exit codes
func TestNonZeroExitCode(t *testing.T) {
	// Create test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := &wsexec.ServerCommand{
			Path: "sh",
			Args: []string{"sh", "-c", "exit 42"},
		}

		if err := cmd.Handle(w, r); err != nil {
			t.Errorf("Server handle error: %v", err)
		}
	}))
	defer server.Close()

	// Create client
	req, err := http.NewRequest("GET", server.URL+"/exec/test/websocket", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}
	req.URL.Scheme = "ws"

	cmd := wsexec.Command(req, "sh", "-c", "exit 42")
	cmd.PingInterval = 100 * time.Millisecond

	// Run should succeed even with non-zero exit
	if err := cmd.Run(); err != nil {
		t.Fatalf("Command failed: %v", err)
	}

	// Check exit code
	if code := cmd.ExitCode(); code != 42 {
		t.Errorf("Expected exit code 42, got %d", code)
	}
}

// TestWorkingDirectoryChange tests setting working directory
func TestWorkingDirectoryChange(t *testing.T) {
	// Create test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := &wsexec.ServerCommand{
			Path: "pwd",
			Args: []string{"pwd"},
			Dir:  "/tmp",
		}

		if err := cmd.Handle(w, r); err != nil {
			t.Errorf("Server handle error: %v", err)
		}
	}))
	defer server.Close()

	// Create client
	req, err := http.NewRequest("GET", server.URL+"/exec/test/websocket", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}
	req.URL.Scheme = "ws"

	var stdout bytes.Buffer
	cmd := wsexec.Command(req, "pwd")
	cmd.Stdout = &stdout
	cmd.PingInterval = 100 * time.Millisecond

	if err := cmd.Run(); err != nil {
		t.Fatalf("Command failed: %v", err)
	}

	// Check output - should be /tmp or /private/tmp (macOS)
	output := strings.TrimSpace(stdout.String())
	if !strings.Contains(output, "/tmp") {
		t.Errorf("Expected output to contain '/tmp', got %q", output)
	}
}

// TestConcurrentCommandExecution tests multiple commands running concurrently
func TestConcurrentCommandExecution(t *testing.T) {
	// Create test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := &wsexec.ServerCommand{
			Path: "echo",
			Args: []string{"echo", "concurrent test"},
		}

		if err := cmd.Handle(w, r); err != nil {
			t.Errorf("Server handle error: %v", err)
		}
	}))
	defer server.Close()

	const numCommands = 5
	results := make([]string, numCommands)
	errors := make([]error, numCommands)

	// Use WaitGroup to wait for all commands
	done := make(chan struct{}, numCommands)

	for i := 0; i < numCommands; i++ {
		go func(index int) {
			defer func() { done <- struct{}{} }()

			// Create client
			req, err := http.NewRequest("GET", server.URL+"/exec/test/websocket", nil)
			if err != nil {
				errors[index] = err
				return
			}
			req.URL.Scheme = "ws"

			var stdout bytes.Buffer
			cmd := wsexec.Command(req, "echo", "concurrent test")
			cmd.Stdout = &stdout
			cmd.PingInterval = 100 * time.Millisecond

			if err := cmd.Run(); err != nil {
				errors[index] = err
				return
			}

			results[index] = strings.TrimSpace(stdout.String())
		}(i)
	}

	// Wait for all commands to complete
	for i := 0; i < numCommands; i++ {
		select {
		case <-done:
			// Command completed
		case <-time.After(5 * time.Second):
			t.Fatal("Timeout waiting for concurrent commands")
		}
	}

	// Check results
	for i := 0; i < numCommands; i++ {
		if errors[i] != nil {
			t.Errorf("Command %d failed: %v", i, errors[i])
		}
		if results[i] != "concurrent test" {
			t.Errorf("Command %d: expected 'concurrent test', got %q", i, results[i])
		}
	}
}
