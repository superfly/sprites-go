package api

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
	"time"
)

func TestHandleCheckpoint(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))

	tests := []struct {
		name                 string
		method               string
		body                 string
		commandResponse      CommandResponse
		expectedStatus       int
		expectedBodyContains string
	}{
		{
			name:   "successful checkpoint",
			method: http.MethodPost,
			body:   `{"checkpoint_id": "test-checkpoint"}`,
			commandResponse: CommandResponse{
				Success: true,
			},
			expectedStatus:       http.StatusAccepted,
			expectedBodyContains: "checkpoint created",
		},
		{
			name:                 "wrong method",
			method:               http.MethodGet,
			expectedStatus:       http.StatusMethodNotAllowed,
			expectedBodyContains: "Method not allowed",
		},
		{
			name:                 "missing checkpoint_id",
			method:               http.MethodPost,
			body:                 `{}`,
			expectedStatus:       http.StatusBadRequest,
			expectedBodyContains: "checkpoint_id is required",
		},
		{
			name:                 "invalid JSON",
			method:               http.MethodPost,
			body:                 `{invalid json}`,
			expectedStatus:       http.StatusBadRequest,
			expectedBodyContains: "Invalid request body",
		},
		{
			name:   "checkpoint failure",
			method: http.MethodPost,
			body:   `{"checkpoint_id": "test-checkpoint"}`,
			commandResponse: CommandResponse{
				Success: false,
				Error:   errors.New("checkpoint failed"),
			},
			expectedStatus:       http.StatusInternalServerError,
			expectedBodyContains: "Failed to create checkpoint",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			commandCh := make(chan Command, 1)
			processManager := newMockProcessManager()

			config := Config{
				ListenAddr: ":8080",
				APIToken:   "test-token",
			}

			server, _ := NewServer(config, commandCh, processManager, logger)

			// Set up command handler
			go func() {
				select {
				case cmd := <-commandCh:
					if cmd.Type == CommandCheckpoint {
						cmd.Response <- tt.commandResponse
					}
				case <-time.After(time.Second):
					t.Error("Timeout waiting for command")
				}
			}()

			// Create request
			req := httptest.NewRequest(tt.method, "/checkpoint", strings.NewReader(tt.body))
			req.Header.Set("Authorization", "Bearer test-token")
			req.Header.Set("Content-Type", "application/json")

			// Execute request
			rr := httptest.NewRecorder()
			server.handleCheckpoint(rr, req)

			// Check status
			if rr.Code != tt.expectedStatus {
				t.Errorf("handler returned wrong status code: got %v want %v", rr.Code, tt.expectedStatus)
			}

			// Check body
			if tt.expectedBodyContains != "" && !strings.Contains(rr.Body.String(), tt.expectedBodyContains) {
				t.Errorf("handler returned unexpected body: got %v want containing %v", rr.Body.String(), tt.expectedBodyContains)
			}
		})
	}
}

func TestHandleRestore(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))

	tests := []struct {
		name                 string
		method               string
		body                 string
		commandResponse      CommandResponse
		expectedStatus       int
		expectedBodyContains string
	}{
		{
			name:   "successful restore initiation",
			method: http.MethodPost,
			body:   `{"checkpoint_id": "test-checkpoint"}`,
			commandResponse: CommandResponse{
				Success: true,
			},
			expectedStatus:       http.StatusAccepted,
			expectedBodyContains: "restore initiated",
		},
		{
			name:                 "wrong method",
			method:               http.MethodGet,
			expectedStatus:       http.StatusMethodNotAllowed,
			expectedBodyContains: "Method not allowed",
		},
		{
			name:                 "missing checkpoint_id",
			method:               http.MethodPost,
			body:                 `{}`,
			expectedStatus:       http.StatusBadRequest,
			expectedBodyContains: "checkpoint_id is required",
		},
		{
			name:                 "invalid JSON",
			method:               http.MethodPost,
			body:                 `{invalid json}`,
			expectedStatus:       http.StatusBadRequest,
			expectedBodyContains: "Invalid request body",
		},
		{
			name:   "restore initiation failure",
			method: http.MethodPost,
			body:   `{"checkpoint_id": "test-checkpoint"}`,
			commandResponse: CommandResponse{
				Success: false,
				Error:   errors.New("restore failed to start"),
			},
			expectedStatus:       http.StatusInternalServerError,
			expectedBodyContains: "Failed to initiate restore",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			commandCh := make(chan Command, 1)
			processManager := newMockProcessManager()

			config := Config{
				ListenAddr: ":8080",
				APIToken:   "test-token",
			}

			server, _ := NewServer(config, commandCh, processManager, logger)

			// Set up command handler
			go func() {
				select {
				case cmd := <-commandCh:
					if cmd.Type == CommandRestore {
						cmd.Response <- tt.commandResponse
					}
				case <-time.After(time.Second):
					t.Error("Timeout waiting for command")
				}
			}()

			// Create request
			req := httptest.NewRequest(tt.method, "/restore", strings.NewReader(tt.body))
			req.Header.Set("Authorization", "Bearer test-token")
			req.Header.Set("Content-Type", "application/json")

			// Execute request
			rr := httptest.NewRecorder()
			server.handleRestore(rr, req)

			// Check status
			if rr.Code != tt.expectedStatus {
				t.Errorf("handler returned wrong status code: got %v want %v", rr.Code, tt.expectedStatus)
			}

			// Check body
			if tt.expectedBodyContains != "" && !strings.Contains(rr.Body.String(), tt.expectedBodyContains) {
				t.Errorf("handler returned unexpected body: got %v want containing %v", rr.Body.String(), tt.expectedBodyContains)
			}
		})
	}
}

func TestWaitForRunningMiddleware(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	commandCh := make(chan Command)

	tests := []struct {
		name           string
		processRunning bool
		waitTime       time.Duration
		expectedStatus int
		expectedBody   string
	}{
		{
			name:           "process already running",
			processRunning: true,
			expectedStatus: http.StatusOK,
			expectedBody:   "OK",
		},
		{
			name:           "process not running and timeout",
			processRunning: false,
			waitTime:       200 * time.Millisecond,
			expectedStatus: http.StatusServiceUnavailable,
			expectedBody:   "Process not ready",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			processManager := newMockProcessManager()
			processManager.setProcessRunning(tt.processRunning)

			config := Config{
				ListenAddr:  ":8080",
				APIToken:    "test-token",
				MaxWaitTime: tt.waitTime,
			}
			if config.MaxWaitTime == 0 {
				config.MaxWaitTime = 30 * time.Second
			}

			server, _ := NewServer(config, commandCh, processManager, logger)

			// Create test handler
			testHandler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
				w.WriteHeader(http.StatusOK)
				w.Write([]byte("OK"))
			})

			// Wrap with middleware
			handler := server.waitForRunningMiddleware(testHandler)

			// Create request
			req := httptest.NewRequest("GET", "/test", nil)

			// Execute request
			rr := httptest.NewRecorder()
			handler.ServeHTTP(rr, req)

			// Check status
			if rr.Code != tt.expectedStatus {
				t.Errorf("handler returned wrong status code: got %v want %v", rr.Code, tt.expectedStatus)
			}

			// Check body
			if !strings.Contains(rr.Body.String(), tt.expectedBody) {
				t.Errorf("handler returned unexpected body: got %v want containing %v", rr.Body.String(), tt.expectedBody)
			}
		})
	}
}

func TestEndpointIntegration(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	commandCh := make(chan Command, 10)
	processManager := newMockProcessManager()
	processManager.setProcessRunning(true)

	config := Config{
		ListenAddr: ":8080",
		APIToken:   "test-token",
	}

	server, _ := NewServer(config, commandCh, processManager, logger)

	// Set up HTTP test server
	mux := http.NewServeMux()
	server.setupEndpoints(mux)
	ts := httptest.NewServer(mux)
	defer ts.Close()

	// Handle commands in background
	go func() {
		for cmd := range commandCh {
			switch cmd.Type {
			case CommandCheckpoint:
				cmd.Response <- CommandResponse{Success: true}
			case CommandRestore:
				cmd.Response <- CommandResponse{Success: true}
			}
		}
	}()

	// Test checkpoint endpoint with auth
	t.Run("checkpoint with auth", func(t *testing.T) {
		body := bytes.NewReader([]byte(`{"checkpoint_id": "test-123"}`))
		req, _ := http.NewRequest(http.MethodPost, ts.URL+"/checkpoint", body)
		req.Header.Set("Authorization", "Bearer test-token")
		req.Header.Set("Content-Type", "application/json")

		resp, err := http.DefaultClient.Do(req)
		if err != nil {
			t.Fatal(err)
		}
		defer resp.Body.Close()

		if resp.StatusCode != http.StatusAccepted {
			t.Errorf("Expected status %d, got %d", http.StatusAccepted, resp.StatusCode)
		}

		var result map[string]string
		json.NewDecoder(resp.Body).Decode(&result)
		if result["checkpoint_id"] != "test-123" {
			t.Errorf("Expected checkpoint_id test-123, got %s", result["checkpoint_id"])
		}
	})

	// Test checkpoint endpoint without auth
	t.Run("checkpoint without auth", func(t *testing.T) {
		body := bytes.NewReader([]byte(`{"checkpoint_id": "test-123"}`))
		req, _ := http.NewRequest(http.MethodPost, ts.URL+"/checkpoint", body)
		req.Header.Set("Content-Type", "application/json")

		resp, err := http.DefaultClient.Do(req)
		if err != nil {
			t.Fatal(err)
		}
		defer resp.Body.Close()

		if resp.StatusCode != http.StatusUnauthorized {
			t.Errorf("Expected status %d, got %d", http.StatusUnauthorized, resp.StatusCode)
		}
	})
}

func TestExecHandler(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	config := Config{
		APIToken: "test-token",
	}

	t.Run("successful command with stdout", func(t *testing.T) {
		commandCh := make(chan Command, 1)
		mockPM := newMockProcessManager()
		mockPM.setProcessRunning(true)

		server, err := NewServer(config, commandCh, mockPM, logger)
		if err != nil {
			t.Fatalf("Failed to create server: %v", err)
		}

		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{
			"command": ["echo", "hello world"],
			"timeout": 1000000000
		}`))
		req.Header.Set("Content-Type", "application/json")
		req.Header.Set("Authorization", "Bearer test-token")

		rr := httptest.NewRecorder()
		server.handleExec(rr, req)

		if rr.Code != http.StatusOK {
			t.Errorf("handler returned wrong status code: got %v want %v", rr.Code, http.StatusOK)
		}

		// Parse response
		messages := parseExecMessages(t, rr.Body.String())

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
		commandCh := make(chan Command, 1)
		mockPM := newMockProcessManager()
		mockPM.setProcessRunning(true)

		server, _ := NewServer(config, commandCh, mockPM, logger)

		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{
			"command": ["sh", "-c", "echo error >&2"],
			"timeout": 1000000000
		}`))
		req.Header.Set("Content-Type", "application/json")
		req.Header.Set("Authorization", "Bearer test-token")

		rr := httptest.NewRecorder()
		server.handleExec(rr, req)

		messages := parseExecMessages(t, rr.Body.String())

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
		commandCh := make(chan Command, 1)
		mockPM := newMockProcessManager()
		mockPM.setProcessRunning(true)

		server, _ := NewServer(config, commandCh, mockPM, logger)

		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{
			"command": ["sh", "-c", "echo stdout && echo stderr >&2"],
			"timeout": 1000000000
		}`))
		req.Header.Set("Content-Type", "application/json")
		req.Header.Set("Authorization", "Bearer test-token")

		rr := httptest.NewRecorder()
		server.handleExec(rr, req)

		messages := parseExecMessages(t, rr.Body.String())

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
		commandCh := make(chan Command, 1)
		mockPM := newMockProcessManager()
		mockPM.setProcessRunning(true)

		server, _ := NewServer(config, commandCh, mockPM, logger)

		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{
			"command": ["sh", "-c", "exit 42"],
			"timeout": 1000000000
		}`))
		req.Header.Set("Content-Type", "application/json")
		req.Header.Set("Authorization", "Bearer test-token")

		rr := httptest.NewRecorder()
		server.handleExec(rr, req)

		messages := parseExecMessages(t, rr.Body.String())

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
		commandCh := make(chan Command, 1)
		mockPM := newMockProcessManager()
		mockPM.setProcessRunning(true)

		server, _ := NewServer(config, commandCh, mockPM, logger)

		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{
			"command": ["sleep", "10"],
			"timeout": 100000000
		}`))
		req.Header.Set("Content-Type", "application/json")
		req.Header.Set("Authorization", "Bearer test-token")

		rr := httptest.NewRecorder()
		server.handleExec(rr, req)

		messages := parseExecMessages(t, rr.Body.String())

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
		commandCh := make(chan Command, 1)
		mockPM := newMockProcessManager()
		mockPM.setProcessRunning(true)

		server, _ := NewServer(config, commandCh, mockPM, logger)

		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{
			"command": ["/does/not/exist/command"],
			"timeout": 1000000000
		}`))
		req.Header.Set("Content-Type", "application/json")
		req.Header.Set("Authorization", "Bearer test-token")

		rr := httptest.NewRecorder()
		server.handleExec(rr, req)

		// Should fail to start and return error before streaming
		if rr.Code != http.StatusInternalServerError {
			t.Errorf("expected status 500 for non-existent command, got %d", rr.Code)
		}

		if !strings.Contains(rr.Body.String(), "Failed to start command") {
			t.Errorf("expected error about failed to start command, got: %s", rr.Body.String())
		}
	})

	t.Run("empty command array", func(t *testing.T) {
		commandCh := make(chan Command, 1)
		mockPM := newMockProcessManager()
		mockPM.setProcessRunning(true)

		server, _ := NewServer(config, commandCh, mockPM, logger)

		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{
			"command": [],
			"timeout": 1000000000
		}`))
		req.Header.Set("Content-Type", "application/json")
		req.Header.Set("Authorization", "Bearer test-token")

		rr := httptest.NewRecorder()
		server.handleExec(rr, req)

		if rr.Code != http.StatusBadRequest {
			t.Errorf("expected status 400 for empty command, got %d", rr.Code)
		}

		if !strings.Contains(rr.Body.String(), "Command array cannot be empty") {
			t.Errorf("unexpected error message: %s", rr.Body.String())
		}
	})

	t.Run("invalid JSON request", func(t *testing.T) {
		commandCh := make(chan Command, 1)
		mockPM := newMockProcessManager()
		mockPM.setProcessRunning(true)

		server, _ := NewServer(config, commandCh, mockPM, logger)

		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{invalid json`))
		req.Header.Set("Content-Type", "application/json")
		req.Header.Set("Authorization", "Bearer test-token")

		rr := httptest.NewRecorder()
		server.handleExec(rr, req)

		if rr.Code != http.StatusBadRequest {
			t.Errorf("expected status 400 for invalid JSON, got %d", rr.Code)
		}

		if !strings.Contains(rr.Body.String(), "Invalid request body") {
			t.Errorf("unexpected error message: %s", rr.Body.String())
		}
	})

	t.Run("GET method not allowed", func(t *testing.T) {
		commandCh := make(chan Command, 1)
		mockPM := newMockProcessManager()
		mockPM.setProcessRunning(true)

		server, _ := NewServer(config, commandCh, mockPM, logger)

		req := httptest.NewRequest("GET", "/exec", nil)
		req.Header.Set("Authorization", "Bearer test-token")

		rr := httptest.NewRecorder()
		server.handleExec(rr, req)

		if rr.Code != http.StatusMethodNotAllowed {
			t.Errorf("expected status 405 for GET method, got %d", rr.Code)
		}
	})

	t.Run("default timeout applied", func(t *testing.T) {
		commandCh := make(chan Command, 1)
		mockPM := newMockProcessManager()
		mockPM.setProcessRunning(true)

		server, _ := NewServer(config, commandCh, mockPM, logger)

		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{
			"command": ["echo", "test"]
		}`))
		req.Header.Set("Content-Type", "application/json")
		req.Header.Set("Authorization", "Bearer test-token")

		rr := httptest.NewRecorder()
		server.handleExec(rr, req)

		// Should succeed (default timeout is 30s)
		if rr.Code != http.StatusOK {
			t.Errorf("expected status 200, got %d", rr.Code)
		}

		messages := parseExecMessages(t, rr.Body.String())
		if len(messages) != 2 || messages[1].ExitCode != 0 {
			t.Errorf("command should have succeeded with default timeout")
		}
	})

	t.Run("command with large output", func(t *testing.T) {
		commandCh := make(chan Command, 1)
		mockPM := newMockProcessManager()
		mockPM.setProcessRunning(true)

		server, _ := NewServer(config, commandCh, mockPM, logger)

		// Generate a command that outputs many lines
		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{
			"command": ["sh", "-c", "for i in $(seq 1 100); do echo Line $i; done"],
			"timeout": 1000000000
		}`))
		req.Header.Set("Content-Type", "application/json")
		req.Header.Set("Authorization", "Bearer test-token")

		rr := httptest.NewRecorder()
		server.handleExec(rr, req)

		messages := parseExecMessages(t, rr.Body.String())

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
		commandCh := make(chan Command, 1)
		mockPM := newMockProcessManager()
		mockPM.setProcessRunning(true)

		server, _ := NewServer(config, commandCh, mockPM, logger)

		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{
			"command": ["sleep", "10"],
			"timeout": 10000000000
		}`))
		req.Header.Set("Content-Type", "application/json")
		req.Header.Set("Authorization", "Bearer test-token")

		// Create a context we can cancel
		ctx, cancel := context.WithCancel(req.Context())
		req = req.WithContext(ctx)

		rr := httptest.NewRecorder()

		// Start the handler in a goroutine
		done := make(chan bool)
		go func() {
			server.handleExec(rr, req)
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
		messages := parseExecMessages(t, rr.Body.String())
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
		// Create config with wrapper
		wrapperConfig := Config{
			APIToken:           "test-token",
			ExecWrapperCommand: []string{"sh", "-c"},
		}

		commandCh := make(chan Command, 1)
		mockPM := newMockProcessManager()
		mockPM.setProcessRunning(true)

		server, _ := NewServer(wrapperConfig, commandCh, mockPM, logger)

		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{
			"command": ["echo hello"],
			"timeout": 1000000000
		}`))
		req.Header.Set("Content-Type", "application/json")
		req.Header.Set("Authorization", "Bearer test-token")

		rr := httptest.NewRecorder()
		server.handleExec(rr, req)

		if rr.Code != http.StatusOK {
			t.Errorf("handler returned wrong status code: got %v want %v", rr.Code, http.StatusOK)
		}

		messages := parseExecMessages(t, rr.Body.String())

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
		// Create config with TTY wrapper
		ttyConfig := Config{
			APIToken:              "test-token",
			ExecWrapperCommand:    []string{"sh", "-c"},
			ExecTTYWrapperCommand: []string{"sh", "-c"},
		}

		commandCh := make(chan Command, 1)
		mockPM := newMockProcessManager()
		mockPM.setProcessRunning(true)

		server, _ := NewServer(ttyConfig, commandCh, mockPM, logger)

		req := httptest.NewRequest("POST", "/exec", strings.NewReader(`{
			"command": ["echo tty test"],
			"timeout": 1000000000,
			"tty": true
		}`))
		req.Header.Set("Content-Type", "application/json")
		req.Header.Set("Authorization", "Bearer test-token")

		rr := httptest.NewRecorder()
		server.handleExec(rr, req)

		if rr.Code != http.StatusOK {
			t.Errorf("handler returned wrong status code: got %v want %v", rr.Code, http.StatusOK)
		}

		messages := parseExecMessages(t, rr.Body.String())

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
func parseExecMessages(t *testing.T, body string) []ExecMessage {
	var messages []ExecMessage
	lines := strings.Split(strings.TrimSpace(body), "\n")

	for _, line := range lines {
		if line == "" {
			continue
		}

		var msg ExecMessage
		if err := json.Unmarshal([]byte(line), &msg); err != nil {
			t.Fatalf("failed to parse message: %v, line: %s", err, line)
		}
		messages = append(messages, msg)
	}

	return messages
}

func TestExecHandlerWithAuth(t *testing.T) {
	// Test that exec endpoint requires authentication
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	commandCh := make(chan Command, 1)
	mockPM := newMockProcessManager()
	mockPM.setProcessRunning(true)

	config := Config{
		APIToken: "test-token",
	}

	server, err := NewServer(config, commandCh, mockPM, logger)
	if err != nil {
		t.Fatalf("Failed to create server: %v", err)
	}

	// Set up test server
	mux := http.NewServeMux()
	server.setupEndpoints(mux)
	ts := httptest.NewServer(mux)
	defer ts.Close()

	// Test without auth
	resp, err := http.Post(ts.URL+"/exec", "application/json", strings.NewReader(`{"command": ["echo", "test"]}`))
	if err != nil {
		t.Fatalf("Failed to make request: %v", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusUnauthorized {
		t.Errorf("expected 401, got %d", resp.StatusCode)
	}
}

func TestExecHandlerProcessNotRunning(t *testing.T) {
	// Test that exec waits for process to be running
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	commandCh := make(chan Command, 1)
	mockPM := newMockProcessManager()
	mockPM.setProcessRunning(false)

	config := Config{
		APIToken:    "test-token",
		MaxWaitTime: 200 * time.Millisecond, // Short timeout for test
	}

	server, err := NewServer(config, commandCh, mockPM, logger)
	if err != nil {
		t.Fatalf("Failed to create server: %v", err)
	}

	// Set up test server
	mux := http.NewServeMux()
	server.setupEndpoints(mux)
	ts := httptest.NewServer(mux)
	defer ts.Close()

	// Make request with auth
	req, _ := http.NewRequest(http.MethodPost, ts.URL+"/exec", strings.NewReader(`{"command": ["echo", "test"]}`))
	req.Header.Set("Authorization", "Bearer test-token")

	start := time.Now()
	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		t.Fatalf("Failed to make request: %v", err)
	}
	defer resp.Body.Close()
	elapsed := time.Since(start)

	// Should timeout and return 503
	if resp.StatusCode != http.StatusServiceUnavailable {
		t.Errorf("expected 503, got %d", resp.StatusCode)
	}

	// Should have waited approximately MaxWaitTime
	if elapsed < 150*time.Millisecond || elapsed > 300*time.Millisecond {
		t.Errorf("expected wait time around 200ms, got %v", elapsed)
	}
}
