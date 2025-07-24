package terminal

import (
	"bytes"
	"context"
	"fmt"
	"net/http"
	"net/http/httptest"
	"strings"
	"sync"
	"testing"
	"time"
)

// TestWebSocketClientBasicExecution tests basic command execution through the client
func TestWebSocketClientBasicExecution(t *testing.T) {
	tests := []struct {
		name           string
		command        []string
		expectedStdout string
		expectedStderr string
		expectedExit   int
	}{
		{
			name:           "simple echo",
			command:        []string{"echo", "hello world"},
			expectedStdout: "hello world\n",
			expectedStderr: "",
			expectedExit:   0,
		},
		{
			name:           "echo to stderr",
			command:        []string{"sh", "-c", "echo 'error message' >&2"},
			expectedStdout: "",
			expectedStderr: "error message\n",
			expectedExit:   0,
		},
		{
			name:           "both stdout and stderr",
			command:        []string{"sh", "-c", "echo 'stdout'; echo 'stderr' >&2"},
			expectedStdout: "stdout\n",
			expectedStderr: "stderr\n",
			expectedExit:   0,
		},
		{
			name:           "non-zero exit",
			command:        []string{"sh", "-c", "exit 42"},
			expectedStdout: "",
			expectedStderr: "",
			expectedExit:   42,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Create a test session
			session := NewSession(
				WithCommand(tt.command[0], tt.command[1:]...),
				WithTTY(false),
			)

			// Create handler and server
			handler := NewWebSocketHandler(session)
			server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
				if err := handler.Handle(w, r); err != nil {
					t.Errorf("handler error: %v", err)
				}
			}))
			defer server.Close()

			// Convert to WebSocket URL
			wsURL := "ws" + strings.TrimPrefix(server.URL, "http")

			// Create request
			req, err := http.NewRequest("GET", wsURL, nil)
			if err != nil {
				t.Fatalf("failed to create request: %v", err)
			}

			// Create WebSocket client command
			ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
			defer cancel()

			cmd := CommandContext(ctx, req, "test-command")

			// Set up buffers for I/O
			var stdout, stderr bytes.Buffer
			cmd.Stdin = nil
			cmd.Stdout = &stdout
			cmd.Stderr = &stderr
			cmd.Tty = false

			// Run the command
			err = cmd.Run()
			if err != nil {
				t.Fatalf("command failed: %v", err)
			}

			// Check results
			if stdout.String() != tt.expectedStdout {
				t.Errorf("stdout mismatch: got %q, want %q", stdout.String(), tt.expectedStdout)
			}
			if stderr.String() != tt.expectedStderr {
				t.Errorf("stderr mismatch: got %q, want %q", stderr.String(), tt.expectedStderr)
			}
			if cmd.ExitCode() != tt.expectedExit {
				t.Errorf("exit code mismatch: got %d, want %d", cmd.ExitCode(), tt.expectedExit)
			}
		})
	}
}

// TestWebSocketClientLargeOutput tests the client handling 100 lines of output
// This is the client-side equivalent of TestWebSocketDataCompletion
func TestWebSocketClientLargeOutput(t *testing.T) {
	// Create a session that outputs 100 lines
	session := NewSession(
		WithCommand("sh", "-c", "for i in $(seq 1 100); do echo \"Line $i\"; done"),
		WithTTY(false),
	)

	handler := NewWebSocketHandler(session)
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if err := handler.Handle(w, r); err != nil {
			t.Errorf("handler error: %v", err)
		}
	}))
	defer server.Close()

	// Run the test multiple times to catch intermittent issues
	for iteration := 0; iteration < 10; iteration++ {
		t.Run(fmt.Sprintf("iteration_%d", iteration), func(t *testing.T) {
			wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
			req, err := http.NewRequest("GET", wsURL, nil)
			if err != nil {
				t.Fatalf("failed to create request: %v", err)
			}

			ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
			defer cancel()

			cmd := CommandContext(ctx, req, "test-100-lines")

			var stdout bytes.Buffer
			cmd.Stdout = &stdout
			cmd.Stderr = nil
			cmd.Tty = false

			// Measure execution time
			start := time.Now()
			err = cmd.Run()
			duration := time.Since(start)

			if err != nil {
				t.Fatalf("command failed: %v", err)
			}

			// Parse output lines
			output := stdout.String()
			lines := strings.Split(strings.TrimSpace(output), "\n")

			// Should have exactly 100 lines
			if len(lines) != 100 {
				t.Errorf("expected 100 lines, got %d", len(lines))
				if len(lines) > 0 {
					t.Logf("First line: %s", lines[0])
					t.Logf("Last line: %s", lines[len(lines)-1])
				}
				t.Logf("Total output length: %d bytes", len(output))
			}

			// Verify each line
			for i, line := range lines {
				expected := fmt.Sprintf("Line %d", i+1)
				if line != expected {
					t.Errorf("line %d: expected %q, got %q", i, expected, line)
					// Only report first few mismatches to avoid spam
					if i > 5 {
						break
					}
				}
			}

			// Exit code should be 0
			if cmd.ExitCode() != 0 {
				t.Errorf("expected exit code 0, got %d", cmd.ExitCode())
			}

			t.Logf("Successfully received all 100 lines in %v", duration)
		})
	}
}

// TestWebSocketClientStderrLargeOutput tests handling large stderr output
func TestWebSocketClientStderrLargeOutput(t *testing.T) {
	session := NewSession(
		WithCommand("sh", "-c", "for i in $(seq 1 100); do echo \"Error $i\" >&2; done"),
		WithTTY(false),
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
	if err != nil {
		t.Fatalf("failed to create request: %v", err)
	}

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	cmd := CommandContext(ctx, req, "test-stderr-100")

	var stdout, stderr bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr
	cmd.Tty = false

	err = cmd.Run()
	if err != nil {
		t.Fatalf("command failed: %v", err)
	}

	// Should have no stdout
	if stdout.String() != "" {
		t.Errorf("expected no stdout, got %q", stdout.String())
	}

	// Check stderr
	stderrLines := strings.Split(strings.TrimSpace(stderr.String()), "\n")
	if len(stderrLines) != 100 {
		t.Errorf("expected 100 stderr lines, got %d", len(stderrLines))
	}

	// Verify content
	for i := 0; i < len(stderrLines) && i < 100; i++ {
		expected := fmt.Sprintf("Error %d", i+1)
		if stderrLines[i] != expected {
			t.Errorf("stderr line %d: expected %q, got %q", i, expected, stderrLines[i])
			break
		}
	}
}

// TestWebSocketClientRaceCondition tests race conditions with fast-exiting commands
func TestWebSocketClientRaceCondition(t *testing.T) {
	testCases := []struct {
		name        string
		command     []string
		expectedOut string
		expectedErr string
	}{
		{
			name:        "single character",
			command:     []string{"sh", "-c", "printf 'x'"},
			expectedOut: "x",
			expectedErr: "",
		},
		{
			name:        "single line",
			command:     []string{"echo", "1"},
			expectedOut: "1\n",
			expectedErr: "",
		},
		{
			name:        "stderr only fast exit",
			command:     []string{"sh", "-c", "echo 'quick' >&2"},
			expectedOut: "",
			expectedErr: "quick\n",
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			// Run multiple times to catch race conditions
			successCount := 0
			const iterations = 20

			for i := 0; i < iterations; i++ {
				session := NewSession(
					WithCommand(tc.command[0], tc.command[1:]...),
					WithTTY(false),
				)

				handler := NewWebSocketHandler(session)
				server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
					if err := handler.Handle(w, r); err != nil {
						t.Errorf("handler error: %v", err)
					}
				}))

				wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
				req, _ := http.NewRequest("GET", wsURL, nil)

				ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
				cmd := CommandContext(ctx, req, "race-test")

				var stdout, stderr bytes.Buffer
				cmd.Stdout = &stdout
				cmd.Stderr = &stderr
				cmd.Tty = false

				err := cmd.Run()
				server.Close()
				cancel()

				if err != nil {
					continue
				}

				if stdout.String() == tc.expectedOut && stderr.String() == tc.expectedErr && cmd.ExitCode() == 0 {
					successCount++
				}
			}

			// Should succeed every time - no race conditions allowed
			if successCount != iterations {
				t.Errorf("Race condition detected: only %d/%d iterations succeeded", successCount, iterations)
			}
		})
	}
}

// TestWebSocketClientConcurrent tests concurrent command execution
func TestWebSocketClientConcurrent(t *testing.T) {
	const concurrency = 10

	// Create a shared server that can handle multiple connections
	mux := http.NewServeMux()
	mux.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
		// Each request gets its own session
		session := NewSession(
			WithCommand("sh", "-c", fmt.Sprintf("echo 'worker %s'", r.URL.Query().Get("id"))),
			WithTTY(false),
		)
		handler := NewWebSocketHandler(session)
		if err := handler.Handle(w, r); err != nil {
			t.Errorf("handler error: %v", err)
		}
	})

	server := httptest.NewServer(mux)
	defer server.Close()

	var wg sync.WaitGroup
	errors := make(chan error, concurrency)

	for i := 0; i < concurrency; i++ {
		wg.Add(1)
		go func(id int) {
			defer wg.Done()

			wsURL := fmt.Sprintf("ws%s/?id=%d", strings.TrimPrefix(server.URL, "http"), id)
			req, err := http.NewRequest("GET", wsURL, nil)
			if err != nil {
				errors <- fmt.Errorf("failed to create request: %v", err)
				return
			}

			ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
			defer cancel()

			cmd := CommandContext(ctx, req, fmt.Sprintf("worker-%d", id))

			var stdout bytes.Buffer
			cmd.Stdout = &stdout
			cmd.Tty = false

			if err := cmd.Run(); err != nil {
				errors <- fmt.Errorf("command failed: %v", err)
				return
			}

			expected := fmt.Sprintf("worker %d\n", id)
			if stdout.String() != expected {
				errors <- fmt.Errorf("worker %d: expected %q, got %q", id, expected, stdout.String())
			}
		}(i)
	}

	wg.Wait()
	close(errors)

	// Check for errors
	var errorCount int
	for err := range errors {
		t.Errorf("concurrent execution error: %v", err)
		errorCount++
	}

	if errorCount > 0 {
		t.Errorf("had %d errors in concurrent execution", errorCount)
	}
}

// TestWebSocketClientBufferBoundaries tests output at various buffer sizes
func TestWebSocketClientBufferBoundaries(t *testing.T) {
	sizes := []int{
		1,    // Single byte
		64,   // Small buffer
		1024, // 1KB
		4096, // 4KB (page size)
		8192, // 8KB
	}

	for _, size := range sizes {
		t.Run(fmt.Sprintf("size_%d", size), func(t *testing.T) {
			// Generate exact size output
			data := strings.Repeat("A", size)
			session := NewSession(
				WithCommand("sh", "-c", fmt.Sprintf("printf '%s'", data)),
				WithTTY(false),
			)

			handler := NewWebSocketHandler(session)
			server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
				if err := handler.Handle(w, r); err != nil {
					t.Errorf("handler error: %v", err)
				}
			}))
			defer server.Close()

			wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
			req, _ := http.NewRequest("GET", wsURL, nil)

			ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
			defer cancel()

			cmd := CommandContext(ctx, req, "buffer-test")

			var stdout bytes.Buffer
			cmd.Stdout = &stdout
			cmd.Tty = false

			err := cmd.Run()
			if err != nil {
				t.Fatalf("command failed: %v", err)
			}

			if stdout.String() != data {
				t.Errorf("output mismatch: expected %d bytes, got %d", size, len(stdout.String()))
			}
		})
	}
}

// TestWebSocketClientWithTTY tests TTY mode
func TestWebSocketClientWithTTY(t *testing.T) {
	session := NewSession(
		WithCommand("echo", "hello tty"),
		WithTTY(true),
		WithTerminalSize(80, 24),
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
	if err != nil {
		t.Fatalf("failed to create request: %v", err)
	}

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	cmd := CommandContext(ctx, req, "tty-test")

	var stdout bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Tty = true

	err = cmd.Run()
	if err != nil {
		t.Fatalf("command failed: %v", err)
	}

	// In TTY mode, output might have additional formatting
	output := stdout.String()
	if !strings.Contains(output, "hello tty") {
		t.Errorf("expected output to contain 'hello tty', got %q", output)
	}
}

// TestWebSocketClientTextMessages tests handling of text messages (e.g., port notifications)
func TestWebSocketClientTextMessages(t *testing.T) {
	session := NewSession(
		WithCommand("echo", "test"),
		WithTTY(false),
	)

	// Track if text message handler was called
	var textMessageReceived bool
	var mu sync.Mutex

	handler := NewWebSocketHandler(session).WithOnConnected(func(sender TextMessageSender) {
		// Send a text message
		sender.SendTextMessage([]byte(`{"type":"port","port":8080,"state":"open"}`))
	})

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if err := handler.Handle(w, r); err != nil {
			t.Errorf("handler error: %v", err)
		}
	}))
	defer server.Close()

	wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
	req, _ := http.NewRequest("GET", wsURL, nil)

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	cmd := CommandContext(ctx, req, "text-msg-test")
	cmd.Tty = false

	// Set text message handler
	cmd.TextMessageHandler = func(data []byte) {
		mu.Lock()
		textMessageReceived = true
		mu.Unlock()

		// Verify message content
		expected := `{"type":"port","port":8080,"state":"open"}`
		if string(data) != expected {
			t.Errorf("unexpected text message: got %q, want %q", string(data), expected)
		}
	}

	err := cmd.Run()
	if err != nil {
		t.Fatalf("command failed: %v", err)
	}

	mu.Lock()
	if !textMessageReceived {
		t.Error("text message handler was not called")
	}
	mu.Unlock()
}
