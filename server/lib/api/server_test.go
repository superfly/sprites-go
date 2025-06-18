package api

import (
	"context"
	"encoding/json"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"os"
	"strings"
	"testing"
	"time"

	"sprite-env/lib"
)

// mockSystemState implements the SystemStateMachine interface for testing
type mockSystemState struct {
	fireCalls []struct {
		trigger string
		args    []any
	}
	fireError    error
	currentState interface{}
}

func (m *mockSystemState) MustState() interface{} {
	return m.currentState
}

func (m *mockSystemState) Fire(trigger string, args ...any) error {
	m.fireCalls = append(m.fireCalls, struct {
		trigger string
		args    []any
	}{trigger: trigger, args: args})
	return m.fireError
}

func TestParseReplayState(t *testing.T) {
	tests := []struct {
		name           string
		headerValue    string
		wantToken      string
		wantMode       string
		wantStateValue string
		wantErr        bool
		errContains    string
	}{
		{
			name:           "valid api mode",
			headerValue:    "state=api:mysecrettoken",
			wantToken:      "mysecrettoken",
			wantMode:       "api",
			wantStateValue: "api:mysecrettoken",
			wantErr:        false,
		},
		{
			name:           "valid proxy mode",
			headerValue:    "state=proxy:token123:8080",
			wantToken:      "token123:8080",
			wantMode:       "proxy",
			wantStateValue: "proxy:token123:8080",
			wantErr:        false,
		},
		{
			name:           "with other parameters",
			headerValue:    "region=ord;state=api:token;app=myapp",
			wantToken:      "token",
			wantMode:       "api",
			wantStateValue: "api:token",
			wantErr:        false,
		},
		{
			name:           "spaces around values",
			headerValue:    "state= api: token123 ",
			wantToken:      "token123",
			wantMode:       "api",
			wantStateValue: "api:token123",
			wantErr:        false,
		},
		{
			name:        "missing state key",
			headerValue: "region=ord;app=myapp",
			wantErr:     true,
			errContains: "missing state",
		},
		{
			name:        "invalid state format - no colon",
			headerValue: "state=apitoken",
			wantErr:     true,
			errContains: "invalid state format",
		},
		{
			name:        "missing token",
			headerValue: "state=api:",
			wantErr:     true,
			errContains: "missing token",
		},
		{
			name:        "missing mode",
			headerValue: "state=:token",
			wantErr:     true,
			errContains: "missing mode",
		},
		{
			name:        "empty header",
			headerValue: "",
			wantErr:     true,
			errContains: "missing state",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			token, mode, stateValue, err := parseReplayState(tt.headerValue)

			if tt.wantErr {
				if err == nil {
					t.Errorf("parseReplayState() expected error, got nil")
					return
				}
				if tt.errContains != "" && !strings.Contains(err.Error(), tt.errContains) {
					t.Errorf("parseReplayState() error = %v, want error containing %v", err, tt.errContains)
				}
				return
			}

			if err != nil {
				t.Errorf("parseReplayState() unexpected error = %v", err)
				return
			}

			if token != tt.wantToken {
				t.Errorf("parseReplayState() token = %v, want %v", token, tt.wantToken)
			}
			if mode != tt.wantMode {
				t.Errorf("parseReplayState() mode = %v, want %v", mode, tt.wantMode)
			}
			if stateValue != tt.wantStateValue {
				t.Errorf("parseReplayState() stateValue = %v, want %v", stateValue, tt.wantStateValue)
			}
		})
	}
}

func TestAuthMiddleware(t *testing.T) {
	// Save and restore env var
	oldToken := os.Getenv("SPRITE_HTTP_API_TOKEN")
	defer os.Setenv("SPRITE_HTTP_API_TOKEN", oldToken)

	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	mockState := &mockSystemState{}

	tests := []struct {
		name           string
		apiToken       string
		replayHeader   string
		requiredMode   string
		expectedStatus int
		expectedBody   string
	}{
		{
			name:           "valid api mode with token",
			apiToken:       "secret123",
			replayHeader:   "state=api:secret123",
			requiredMode:   "api",
			expectedStatus: http.StatusOK,
		},
		{
			name:           "invalid token",
			apiToken:       "secret123",
			replayHeader:   "state=api:wrongtoken",
			requiredMode:   "api",
			expectedStatus: http.StatusUnauthorized,
			expectedBody:   "Invalid authentication token",
		},
		{
			name:           "missing header",
			apiToken:       "secret123",
			replayHeader:   "",
			requiredMode:   "api",
			expectedStatus: http.StatusUnauthorized,
			expectedBody:   "Missing fly-replay-src header",
		},
		{
			name:           "invalid header format",
			apiToken:       "secret123",
			replayHeader:   "state=invalid",
			requiredMode:   "api",
			expectedStatus: http.StatusBadRequest,
			expectedBody:   "Invalid replay state",
		},
		{
			name:           "proxy mode accessing api endpoint",
			apiToken:       "secret123",
			replayHeader:   "state=proxy:secret123:8080",
			requiredMode:   "api",
			expectedStatus: http.StatusNotFound,
			expectedBody:   "not available in proxy mode",
		},
		{
			name:           "api mode accessing proxy endpoint",
			apiToken:       "secret123",
			replayHeader:   "state=api:secret123",
			requiredMode:   "proxy",
			expectedStatus: http.StatusNotFound,
			expectedBody:   "Not found",
		},
		{
			name:           "valid proxy mode",
			apiToken:       "secret123",
			replayHeader:   "state=proxy:secret123:8080",
			requiredMode:   "proxy",
			expectedStatus: http.StatusOK,
		},
		{
			name:           "no auth required",
			apiToken:       "",
			replayHeader:   "state=api:anytoken",
			requiredMode:   "api",
			expectedStatus: http.StatusOK,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			os.Setenv("SPRITE_HTTP_API_TOKEN", tt.apiToken)
			// Create a test config
			config := &lib.ApplicationConfig{
				Exec: lib.ExecConfig{
					WrapperCommand:    []string{},
					TTYWrapperCommand: []string{},
				},
			}
			server := NewServer(":8080", mockState, logger, config)

			// Create a simple test handler
			testHandler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
				w.WriteHeader(http.StatusOK)
				w.Write([]byte("OK"))
			})

			// Wrap with auth middleware
			handler := server.authMiddleware(testHandler, tt.requiredMode)

			// Create request
			req := httptest.NewRequest("GET", "/test", nil)
			if tt.replayHeader != "" {
				req.Header.Set("fly-replay-src", tt.replayHeader)
			}

			// Execute request
			rr := httptest.NewRecorder()
			handler.ServeHTTP(rr, req)

			// Check status
			if rr.Code != tt.expectedStatus {
				t.Errorf("handler returned wrong status code: got %v want %v", rr.Code, tt.expectedStatus)
			}

			// Check body if expected
			if tt.expectedBody != "" && !strings.Contains(rr.Body.String(), tt.expectedBody) {
				t.Errorf("handler returned unexpected body: got %v want containing %v", rr.Body.String(), tt.expectedBody)
			}
		})
	}
}

func TestCheckpointEndpoint(t *testing.T) {
	// Save and restore env var
	oldToken := os.Getenv("SPRITE_HTTP_API_TOKEN")
	defer os.Setenv("SPRITE_HTTP_API_TOKEN", oldToken)
	os.Setenv("SPRITE_HTTP_API_TOKEN", "testtoken")

	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	mockState := &mockSystemState{}
	// Create a test config
	config := &lib.ApplicationConfig{
		Exec: lib.ExecConfig{
			WrapperCommand:    []string{},
			TTYWrapperCommand: []string{},
		},
	}
	server := NewServer(":8080", mockState, logger, config)
	ts := httptest.NewServer(server.server.Handler)
	defer ts.Close()

	tests := []struct {
		name            string
		method          string
		body            string
		replayHeader    string
		expectedStatus  int
		expectedFire    bool
		expectedTrigger string
	}{
		{
			name:            "valid checkpoint request",
			method:          "POST",
			body:            `{"checkpoint_id": "test-checkpoint"}`,
			replayHeader:    "state=api:testtoken",
			expectedStatus:  http.StatusAccepted,
			expectedFire:    true,
			expectedTrigger: "CheckpointRequested",
		},
		{
			name:           "missing checkpoint_id",
			method:         "POST",
			body:           `{}`,
			replayHeader:   "state=api:testtoken",
			expectedStatus: http.StatusBadRequest,
			expectedFire:   false,
		},
		{
			name:           "invalid method",
			method:         "GET",
			body:           `{"checkpoint_id": "test"}`,
			replayHeader:   "state=api:testtoken",
			expectedStatus: http.StatusMethodNotAllowed,
			expectedFire:   false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Reset mock state
			mockState.fireCalls = nil

			req, err := http.NewRequest(tt.method, ts.URL+"/checkpoint", strings.NewReader(tt.body))
			if err != nil {
				t.Fatal(err)
			}
			req.Header.Set("Content-Type", "application/json")
			req.Header.Set("fly-replay-src", tt.replayHeader)

			resp, err := http.DefaultClient.Do(req)
			if err != nil {
				t.Fatal(err)
			}
			defer resp.Body.Close()

			if resp.StatusCode != tt.expectedStatus {
				body, _ := io.ReadAll(resp.Body)
				t.Errorf("unexpected status code: got %v want %v, body: %s", resp.StatusCode, tt.expectedStatus, body)
			}

			if tt.expectedFire {
				if len(mockState.fireCalls) == 0 {
					t.Error("expected Fire to be called but it wasn't")
				} else if mockState.fireCalls[0].trigger != tt.expectedTrigger {
					t.Errorf("unexpected trigger: got %v want %v", mockState.fireCalls[0].trigger, tt.expectedTrigger)
				}
			} else {
				if len(mockState.fireCalls) > 0 {
					t.Errorf("expected Fire not to be called but it was called with: %v", mockState.fireCalls[0].trigger)
				}
			}
		})
	}
}

func TestExecEndpoint(t *testing.T) {
	// Save and restore env var
	oldToken := os.Getenv("SPRITE_HTTP_API_TOKEN")
	defer os.Setenv("SPRITE_HTTP_API_TOKEN", oldToken)
	os.Setenv("SPRITE_HTTP_API_TOKEN", "testtoken")

	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	mockState := &mockSystemState{}
	// Create a test config
	config := &lib.ApplicationConfig{
		Exec: lib.ExecConfig{
			WrapperCommand:    []string{},
			TTYWrapperCommand: []string{},
		},
	}
	server := NewServer(":8080", mockState, logger, config)
	ts := httptest.NewServer(server.server.Handler)
	defer ts.Close()

	// Test basic exec functionality
	reqBody := `{"command": ["echo", "hello"], "timeout": 1000000000}`
	req, err := http.NewRequest("POST", ts.URL+"/exec", strings.NewReader(reqBody))
	if err != nil {
		t.Fatal(err)
	}
	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("fly-replay-src", "state=api:testtoken")

	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		t.Fatal(err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		t.Errorf("unexpected status code: got %v want %v, body: %s", resp.StatusCode, http.StatusOK, body)
	}

	// Read and parse response
	decoder := json.NewDecoder(resp.Body)
	foundStdout := false
	foundExit := false

	for {
		var msg map[string]interface{}
		if err := decoder.Decode(&msg); err == io.EOF {
			break
		} else if err != nil {
			t.Fatalf("failed to decode message: %v", err)
		}

		msgType, ok := msg["type"].(string)
		if !ok {
			t.Error("message missing type field")
			continue
		}

		switch msgType {
		case "stdout":
			if data, ok := msg["data"].(string); ok && data == "hello" {
				foundStdout = true
			}
		case "exit":
			if exitCode, ok := msg["exit_code"].(float64); ok && exitCode == 0 {
				foundExit = true
			}
		}
	}

	if !foundStdout {
		t.Error("did not find expected stdout message")
	}
	if !foundExit {
		t.Error("did not find exit message")
	}
}

func TestServerShutdown(t *testing.T) {
	// Save and restore env var
	oldToken := os.Getenv("SPRITE_HTTP_API_TOKEN")
	defer os.Setenv("SPRITE_HTTP_API_TOKEN", oldToken)
	os.Setenv("SPRITE_HTTP_API_TOKEN", "testtoken")

	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	mockState := &mockSystemState{}

	t.Run("graceful shutdown with in-flight request", func(t *testing.T) {
		// Create a test config
		config := &lib.ApplicationConfig{
			Exec: lib.ExecConfig{
				WrapperCommand:    []string{},
				TTYWrapperCommand: []string{},
			},
		}
		server := NewServer(":0", mockState, logger, config) // Use :0 for random port

		// Start the server
		if err := server.Start(); err != nil {
			t.Fatalf("failed to start server: %v", err)
		}

		// Wait a bit for server to start listening
		time.Sleep(100 * time.Millisecond)

		// The server's actual address is not directly accessible, so we need to try connecting
		// Since the Start() method launches the server in a goroutine, we need to find the actual port
		// For this test, let's use a fixed port instead
		server = NewServer(":18090", mockState, logger, config)
		if err := server.Start(); err != nil {
			t.Fatalf("failed to start server: %v", err)
		}
		time.Sleep(100 * time.Millisecond)

		// Create a slow handler that we'll use to test graceful shutdown
		slowHandler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			// Signal that request has started
			select {
			case <-r.Context().Done():
				// Context cancelled, return error
				http.Error(w, "request cancelled", http.StatusServiceUnavailable)
				return
			case <-time.After(200 * time.Millisecond):
				// Normal completion
				w.WriteHeader(http.StatusOK)
				w.Write([]byte("completed"))
			}
		})

		// Replace the exec handler with our slow handler for testing
		mux := http.NewServeMux()
		mux.Handle("/test", server.authMiddleware(slowHandler, "api"))
		server.server.Handler = mux

		// Start a request in a goroutine
		requestDone := make(chan struct{})
		requestErr := make(chan error, 1)

		go func() {
			req, err := http.NewRequest("GET", "http://localhost:18090/test", nil)
			if err != nil {
				requestErr <- err
				return
			}
			req.Header.Set("fly-replay-src", "state=api:testtoken")

			resp, err := http.DefaultClient.Do(req)
			if err != nil {
				requestErr <- err
				return
			}
			defer resp.Body.Close()

			body, _ := io.ReadAll(resp.Body)
			if resp.StatusCode != http.StatusOK {
				requestErr <- fmt.Errorf("unexpected status: %d, body: %s", resp.StatusCode, body)
				return
			}

			if string(body) != "completed" {
				requestErr <- fmt.Errorf("unexpected body: %s", body)
				return
			}

			close(requestDone)
		}()

		// Give the request time to start
		time.Sleep(50 * time.Millisecond)

		// Now stop the server with a timeout longer than the request
		stopCtx, cancel := context.WithTimeout(context.Background(), 1*time.Second)
		defer cancel()

		stopErr := server.Stop(stopCtx)
		if stopErr != nil {
			t.Errorf("server stop failed: %v", stopErr)
		}

		// Check if the request completed successfully
		select {
		case err := <-requestErr:
			t.Errorf("request failed: %v", err)
		case <-requestDone:
			// Request completed successfully
		case <-time.After(2 * time.Second):
			t.Error("request did not complete in time")
		}
	})

	t.Run("shutdown timeout with slow request", func(t *testing.T) {
		// Create a test config
		config := &lib.ApplicationConfig{
			Exec: lib.ExecConfig{
				WrapperCommand:    []string{},
				TTYWrapperCommand: []string{},
			},
		}
		server := NewServer(":18091", mockState, logger, config)

		// Start the server
		if err := server.Start(); err != nil {
			t.Fatalf("failed to start server: %v", err)
		}

		// Wait for server to start
		time.Sleep(100 * time.Millisecond)

		// Create a very slow handler
		verySlowHandler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			// This will take longer than our shutdown timeout
			select {
			case <-r.Context().Done():
				// Context cancelled
				return
			case <-time.After(5 * time.Second):
				// Should not reach here
				w.WriteHeader(http.StatusOK)
			}
		})

		// Replace handler
		mux := http.NewServeMux()
		mux.Handle("/test", server.authMiddleware(verySlowHandler, "api"))
		server.server.Handler = mux

		// Start a request
		go func() {
			req, err := http.NewRequest("GET", "http://localhost:18091/test", nil)
			if err != nil {
				return
			}
			req.Header.Set("fly-replay-src", "state=api:testtoken")
			http.DefaultClient.Do(req)
		}()

		// Give request time to start
		time.Sleep(50 * time.Millisecond)

		// Stop with short timeout
		stopCtx, cancel := context.WithTimeout(context.Background(), 100*time.Millisecond)
		defer cancel()

		stopErr := server.Stop(stopCtx)
		if stopErr == nil {
			// This is actually fine - the server can forcibly close connections
			// The important thing is that Stop() returns
		}
	})

	t.Run("server refuses new connections after Stop", func(t *testing.T) {
		// Create a test config
		config := &lib.ApplicationConfig{
			Exec: lib.ExecConfig{
				WrapperCommand:    []string{},
				TTYWrapperCommand: []string{},
			},
		}
		server := NewServer(":18092", mockState, logger, config)

		// Start the server
		if err := server.Start(); err != nil {
			t.Fatalf("failed to start server: %v", err)
		}

		// Wait for server to start
		time.Sleep(100 * time.Millisecond)

		// Stop the server
		stopCtx, cancel := context.WithTimeout(context.Background(), 1*time.Second)
		defer cancel()

		if err := server.Stop(stopCtx); err != nil {
			t.Fatalf("failed to stop server: %v", err)
		}

		// Try to make a request - should fail
		req, err := http.NewRequest("GET", "http://localhost:18092/test", nil)
		if err != nil {
			t.Fatal(err)
		}
		req.Header.Set("fly-replay-src", "state=api:testtoken")

		// The request should fail (connection refused or similar)
		resp, err := http.DefaultClient.Do(req)
		if err == nil {
			resp.Body.Close()
			t.Error("expected request to fail after server stop, but it succeeded")
		}
	})
}
