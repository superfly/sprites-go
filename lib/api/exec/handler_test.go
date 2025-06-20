package exec

import (
	"context"
	"encoding/json"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
	"time"

	"lib"
)

func TestExecHandler(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	// Create a test config with no wrappers
	config := &lib.ApplicationConfig{
		Exec: lib.ExecConfig{
			WrapperCommand:    []string{},
			TTYWrapperCommand: []string{},
		},
	}
	handler := NewHandler(logger, config)

	t.Run("successful command with stdout", func(t *testing.T) {
		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{
			"command": ["echo", "hello world"],
			"timeout": 1000000000
		}`))
		req.Header.Set("Content-Type", "application/json")

		rr := httptest.NewRecorder()
		handler.ServeHTTP(rr, req)

		if rr.Code != http.StatusOK {
			t.Errorf("handler returned wrong status code: got %v want %v", rr.Code, http.StatusOK)
		}

		// Parse response
		messages := parseMessages(t, rr.Body.String())

		// Should have stdout and exit messages
		if len(messages) != 2 {
			t.Errorf("expected 2 messages, got %d", len(messages))
		}

		// Check stdout message
		if messages[0].Type != "stdout" || messages[0].Data != "hello world" {
			t.Errorf("unexpected stdout message: %+v", messages[0])
		}

		// Check exit message
		if messages[1].Type != "exit" || messages[1].ExitCode != 0 {
			t.Errorf("unexpected exit message: %+v", messages[1])
		}
	})

	t.Run("command with stderr output", func(t *testing.T) {
		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{
			"command": ["sh", "-c", "echo error >&2"],
			"timeout": 1000000000
		}`))
		req.Header.Set("Content-Type", "application/json")

		rr := httptest.NewRecorder()
		handler.ServeHTTP(rr, req)

		messages := parseMessages(t, rr.Body.String())

		// Should have stderr and exit messages
		if len(messages) != 2 {
			t.Errorf("expected 2 messages, got %d", len(messages))
		}

		// Check stderr message
		if messages[0].Type != "stderr" || messages[0].Data != "error" {
			t.Errorf("unexpected stderr message: %+v", messages[0])
		}

		// Check exit code is 0 (command succeeded)
		if messages[1].Type != "exit" || messages[1].ExitCode != 0 {
			t.Errorf("unexpected exit message: %+v", messages[1])
		}
	})

	t.Run("command with both stdout and stderr", func(t *testing.T) {
		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{
			"command": ["sh", "-c", "echo stdout && echo stderr >&2"],
			"timeout": 1000000000
		}`))
		req.Header.Set("Content-Type", "application/json")

		rr := httptest.NewRecorder()
		handler.ServeHTTP(rr, req)

		messages := parseMessages(t, rr.Body.String())

		// Should have stdout, stderr, and exit messages
		if len(messages) != 3 {
			t.Errorf("expected 3 messages, got %d: %+v", len(messages), messages)
		}

		// Find each message type
		var foundStdout, foundStderr, foundExit bool
		for _, msg := range messages {
			switch msg.Type {
			case "stdout":
				if msg.Data == "stdout" {
					foundStdout = true
				}
			case "stderr":
				if msg.Data == "stderr" {
					foundStderr = true
				}
			case "exit":
				if msg.ExitCode == 0 {
					foundExit = true
				}
			}
		}

		if !foundStdout || !foundStderr || !foundExit {
			t.Errorf("missing expected messages: stdout=%v, stderr=%v, exit=%v", foundStdout, foundStderr, foundExit)
		}
	})

	t.Run("command that exits with non-zero code", func(t *testing.T) {
		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{
			"command": ["sh", "-c", "exit 42"],
			"timeout": 1000000000
		}`))
		req.Header.Set("Content-Type", "application/json")

		rr := httptest.NewRecorder()
		handler.ServeHTTP(rr, req)

		messages := parseMessages(t, rr.Body.String())

		// Should have just exit message
		if len(messages) != 1 {
			t.Errorf("expected 1 message, got %d", len(messages))
		}

		// Check exit code
		if messages[0].Type != "exit" || messages[0].ExitCode != 42 {
			t.Errorf("unexpected exit code: %+v", messages[0])
		}
	})

	t.Run("command that times out", func(t *testing.T) {
		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{
			"command": ["sleep", "10"],
			"timeout": 100000000
		}`))
		req.Header.Set("Content-Type", "application/json")

		rr := httptest.NewRecorder()
		handler.ServeHTTP(rr, req)

		messages := parseMessages(t, rr.Body.String())

		// Should have exit message with error
		if len(messages) != 1 {
			t.Errorf("expected 1 message, got %d", len(messages))
		}

		// Check exit indicates timeout/killed
		exitMsg := messages[0]
		if exitMsg.Type != "exit" {
			t.Errorf("expected exit message, got %s", exitMsg.Type)
		}

		// Timeout should result in exit code -1 (or sometimes signal-based exit codes like 137 for SIGKILL)
		if exitMsg.ExitCode == 0 {
			t.Errorf("expected non-zero exit code for timeout, got %d", exitMsg.ExitCode)
		}
	})

	t.Run("non-existent command", func(t *testing.T) {
		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{
			"command": ["/does/not/exist/command"],
			"timeout": 1000000000
		}`))
		req.Header.Set("Content-Type", "application/json")

		rr := httptest.NewRecorder()
		handler.ServeHTTP(rr, req)

		// Should fail to start and return error before streaming
		if rr.Code != http.StatusInternalServerError {
			t.Errorf("expected status 500 for non-existent command, got %d", rr.Code)
		}

		if !strings.Contains(rr.Body.String(), "Failed to start command") {
			t.Errorf("expected error about failed to start command, got: %s", rr.Body.String())
		}
	})

	t.Run("empty command array", func(t *testing.T) {
		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{
			"command": [],
			"timeout": 1000000000
		}`))
		req.Header.Set("Content-Type", "application/json")

		rr := httptest.NewRecorder()
		handler.ServeHTTP(rr, req)

		if rr.Code != http.StatusBadRequest {
			t.Errorf("expected status 400 for empty command, got %d", rr.Code)
		}

		if !strings.Contains(rr.Body.String(), "Command array cannot be empty") {
			t.Errorf("unexpected error message: %s", rr.Body.String())
		}
	})

	t.Run("invalid JSON request", func(t *testing.T) {
		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{invalid json`))
		req.Header.Set("Content-Type", "application/json")

		rr := httptest.NewRecorder()
		handler.ServeHTTP(rr, req)

		if rr.Code != http.StatusBadRequest {
			t.Errorf("expected status 400 for invalid JSON, got %d", rr.Code)
		}

		if !strings.Contains(rr.Body.String(), "Invalid request body") {
			t.Errorf("unexpected error message: %s", rr.Body.String())
		}
	})

	t.Run("GET method not allowed", func(t *testing.T) {
		req := httptest.NewRequest("GET", "/exec", nil)

		rr := httptest.NewRecorder()
		handler.ServeHTTP(rr, req)

		if rr.Code != http.StatusMethodNotAllowed {
			t.Errorf("expected status 405 for GET method, got %d", rr.Code)
		}
	})

	t.Run("default timeout applied", func(t *testing.T) {
		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{
			"command": ["echo", "test"]
		}`))
		req.Header.Set("Content-Type", "application/json")

		rr := httptest.NewRecorder()
		handler.ServeHTTP(rr, req)

		// Should succeed (default timeout is 30s)
		if rr.Code != http.StatusOK {
			t.Errorf("expected status 200, got %d", rr.Code)
		}

		messages := parseMessages(t, rr.Body.String())
		if len(messages) != 2 || messages[1].ExitCode != 0 {
			t.Errorf("command should have succeeded with default timeout")
		}
	})

	t.Run("command with large output", func(t *testing.T) {
		// Generate a command that outputs many lines
		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{
			"command": ["sh", "-c", "for i in $(seq 1 100); do echo Line $i; done"],
			"timeout": 1000000000
		}`))
		req.Header.Set("Content-Type", "application/json")

		rr := httptest.NewRecorder()
		handler.ServeHTTP(rr, req)

		messages := parseMessages(t, rr.Body.String())

		// Should have 100 stdout messages + 1 exit message
		if len(messages) != 101 {
			t.Errorf("expected 101 messages, got %d", len(messages))
		}

		// Verify all stdout messages
		for i := 0; i < 100; i++ {
			expectedData := fmt.Sprintf("Line %d", i+1)
			if messages[i].Type != "stdout" || messages[i].Data != expectedData {
				t.Errorf("unexpected message at index %d: %+v", i, messages[i])
			}
		}

		// Verify exit message
		if messages[100].Type != "exit" || messages[100].ExitCode != 0 {
			t.Errorf("unexpected exit message: %+v", messages[100])
		}
	})

	t.Run("context cancellation during execution", func(t *testing.T) {
		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{
			"command": ["sleep", "10"],
			"timeout": 10000000000
		}`))
		req.Header.Set("Content-Type", "application/json")

		// Create a context we can cancel
		ctx, cancel := context.WithCancel(req.Context())
		req = req.WithContext(ctx)

		rr := httptest.NewRecorder()

		// Start the handler in a goroutine
		done := make(chan bool)
		go func() {
			handler.ServeHTTP(rr, req)
			done <- true
		}()

		// Cancel the context after a short delay
		time.Sleep(50 * time.Millisecond)
		cancel()

		// Wait for handler to complete
		select {
		case <-done:
			// Handler completed
		case <-time.After(1 * time.Second):
			t.Fatal("handler did not complete after context cancellation")
		}

		// Should have received an exit message
		messages := parseMessages(t, rr.Body.String())
		if len(messages) == 0 {
			t.Fatal("expected at least one message")
		}

		lastMsg := messages[len(messages)-1]
		if lastMsg.Type != "exit" {
			t.Errorf("expected exit message, got %s", lastMsg.Type)
		}

		// Context cancellation should result in non-zero exit code
		if lastMsg.ExitCode == 0 {
			t.Errorf("expected non-zero exit code for cancelled command, got %d", lastMsg.ExitCode)
		}
	})

	t.Run("command with wrapper", func(t *testing.T) {
		// Create handler with wrapper configuration
		wrapperConfig := &lib.ApplicationConfig{
			Exec: lib.ExecConfig{
				WrapperCommand:    []string{"sh", "-c"},
				TTYWrapperCommand: []string{},
			},
		}
		wrapperHandler := NewHandler(logger, wrapperConfig)

		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{
			"command": ["echo hello"],
			"timeout": 1000000000
		}`))
		req.Header.Set("Content-Type", "application/json")

		rr := httptest.NewRecorder()
		wrapperHandler.ServeHTTP(rr, req)

		if rr.Code != http.StatusOK {
			t.Errorf("handler returned wrong status code: got %v want %v", rr.Code, http.StatusOK)
		}

		messages := parseMessages(t, rr.Body.String())

		// Should have stdout and exit messages
		if len(messages) != 2 {
			t.Errorf("expected 2 messages, got %d", len(messages))
		}

		// Check stdout message
		if messages[0].Type != "stdout" || messages[0].Data != "hello" {
			t.Errorf("unexpected stdout message: %+v", messages[0])
		}

		// Check exit message
		if messages[1].Type != "exit" || messages[1].ExitCode != 0 {
			t.Errorf("unexpected exit message: %+v", messages[1])
		}
	})

	t.Run("command with TTY wrapper", func(t *testing.T) {
		// Create handler with TTY wrapper configuration
		ttyConfig := &lib.ApplicationConfig{
			Exec: lib.ExecConfig{
				WrapperCommand:    []string{"sh", "-c"},
				TTYWrapperCommand: []string{"sh", "-c"},
			},
		}
		ttyHandler := NewHandler(logger, ttyConfig)

		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{
			"command": ["echo tty test"],
			"timeout": 1000000000,
			"tty": true
		}`))
		req.Header.Set("Content-Type", "application/json")

		rr := httptest.NewRecorder()
		ttyHandler.ServeHTTP(rr, req)

		if rr.Code != http.StatusOK {
			t.Errorf("handler returned wrong status code: got %v want %v", rr.Code, http.StatusOK)
		}

		messages := parseMessages(t, rr.Body.String())

		// Should have output
		found := false
		for _, msg := range messages {
			if msg.Type == "stdout" && strings.Contains(msg.Data, "tty test") {
				found = true
				break
			}
		}

		if !found {
			t.Errorf("expected to find 'tty test' in output, messages: %+v", messages)
		}
	})
}

// Helper function to parse NDJSON messages
func parseMessages(t *testing.T, body string) []Message {
	var messages []Message
	lines := strings.Split(strings.TrimSpace(body), "\n")

	for _, line := range lines {
		if line == "" {
			continue
		}

		var msg Message
		if err := json.Unmarshal([]byte(line), &msg); err != nil {
			t.Fatalf("failed to parse message: %v, line: %s", err, line)
		}
		messages = append(messages, msg)
	}

	return messages
}
