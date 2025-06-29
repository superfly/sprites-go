package handlers

import (
	"io"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
	"time"
)

// Test NewHandlers constructor
func TestNewHandlers(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	config := Config{
		MaxWaitTime: 30 * time.Second,
	}
	mockSys := &mockSystemManager{}

	h := NewHandlers(logger, mockSys, config)

	if h == nil {
		t.Error("NewHandlers returned nil")
	}
}

// Test HandleCheckpoint validates request method
func TestHandleCheckpointMethod(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	config := Config{}
	mockSys := newMockSystemManager()
	h := NewHandlers(logger, mockSys, config)

	req := httptest.NewRequest(http.MethodGet, "/checkpoint", nil)
	rr := httptest.NewRecorder()

	h.HandleCheckpoint(rr, req)

	if rr.Code != http.StatusMethodNotAllowed {
		t.Errorf("expected status %d, got %d", http.StatusMethodNotAllowed, rr.Code)
	}

	if !strings.Contains(rr.Body.String(), "Method not allowed") {
		t.Errorf("expected error message about method not allowed")
	}
}

// Test HandleCheckpointRestore validates request method
func TestHandleCheckpointRestoreMethod(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	config := Config{}
	mockSys := newMockSystemManager()
	h := NewHandlers(logger, mockSys, config)

	req := httptest.NewRequest(http.MethodGet, "/checkpoints/test-cp/restore", nil)
	rr := httptest.NewRecorder()

	h.HandleCheckpointRestore(rr, req)

	if rr.Code != http.StatusMethodNotAllowed {
		t.Errorf("expected status %d, got %d", http.StatusMethodNotAllowed, rr.Code)
	}

	if !strings.Contains(rr.Body.String(), "Method not allowed") {
		t.Errorf("expected error message about method not allowed")
	}
}

// Test HandleProxy validates request method
func TestHandleProxyMethod(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	config := Config{}
	mockSys := &mockSystemManager{}
	h := NewHandlers(logger, mockSys, config)

	req := httptest.NewRequest(http.MethodGet, "/proxy/example.com", nil)
	rr := httptest.NewRecorder()

	h.HandleProxy(rr, req)

	if rr.Code != http.StatusMethodNotAllowed {
		t.Errorf("expected status %d, got %d", http.StatusMethodNotAllowed, rr.Code)
	}

	if !strings.Contains(rr.Body.String(), "Method not allowed") {
		t.Errorf("expected error message about method not allowed")
	}
}

// Test HandleProxy with CONNECT method requires valid host:port
func TestHandleProxyInvalidHost(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	config := Config{}
	mockSys := &mockSystemManager{}
	h := NewHandlers(logger, mockSys, config)

	req := httptest.NewRequest(http.MethodConnect, "/proxy", nil)
	req.Host = "invalid-no-port" // No port in host
	rr := httptest.NewRecorder()

	h.HandleProxy(rr, req)

	if rr.Code != http.StatusBadRequest {
		t.Errorf("expected status %d, got %d", http.StatusBadRequest, rr.Code)
	}

	if !strings.Contains(rr.Body.String(), "Invalid host format") {
		t.Errorf("expected error message about invalid host format")
	}
}

// Test HandleProxy with invalid port numbers
func TestHandleProxyInvalidPort(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	config := Config{}
	mockSys := &mockSystemManager{}
	h := NewHandlers(logger, mockSys, config)

	tests := []struct {
		name     string
		host     string
		expected string
	}{
		{
			name:     "Port too high",
			host:     "localhost:99999",
			expected: "Invalid port number",
		},
		{
			name:     "Port zero",
			host:     "localhost:0",
			expected: "Invalid port number",
		},
		{
			name:     "Negative port",
			host:     "localhost:-1",
			expected: "Invalid port number",
		},
		{
			name:     "Non-numeric port",
			host:     "localhost:abc",
			expected: "Invalid port number",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			req := httptest.NewRequest(http.MethodConnect, "/proxy", nil)
			req.Host = tt.host
			rr := httptest.NewRecorder()

			h.HandleProxy(rr, req)

			if rr.Code != http.StatusBadRequest {
				t.Errorf("expected status %d, got %d", http.StatusBadRequest, rr.Code)
			}

			if !strings.Contains(rr.Body.String(), tt.expected) {
				t.Errorf("expected error message containing '%s', got: %s", tt.expected, rr.Body.String())
			}
		})
	}
}

// Test HandleProxy connection failure to target
func TestHandleProxyConnectionFailure(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	config := Config{}
	mockSys := &mockSystemManager{}
	h := NewHandlers(logger, mockSys, config)

	// Use a port that should be closed
	req := httptest.NewRequest(http.MethodConnect, "/proxy", nil)
	req.Host = "localhost:9999" // Unlikely to be open
	rr := httptest.NewRecorder()

	h.HandleProxy(rr, req)

	if rr.Code != http.StatusBadGateway {
		t.Errorf("expected status %d, got %d", http.StatusBadGateway, rr.Code)
	}

	if !strings.Contains(rr.Body.String(), "Failed to connect to target") {
		t.Errorf("expected error message about connection failure, got: %s", rr.Body.String())
	}
}

// Test HandleDebugCreateZombie validates request method
func TestHandleDebugCreateZombieMethod(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	config := Config{}
	mockSys := &mockSystemManager{}
	h := NewHandlers(logger, mockSys, config)

	req := httptest.NewRequest(http.MethodGet, "/debug/create-zombie", nil)
	rr := httptest.NewRecorder()

	h.HandleDebugCreateZombie(rr, req)

	if rr.Code != http.StatusMethodNotAllowed {
		t.Errorf("expected status %d, got %d", http.StatusMethodNotAllowed, rr.Code)
	}

	if !strings.Contains(rr.Body.String(), "Method not allowed") {
		t.Errorf("expected error message about method not allowed")
	}
}

// Test HandleDebugCheckProcess validates request method
func TestHandleDebugCheckProcessMethod(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	config := Config{}
	mockSys := &mockSystemManager{}
	h := NewHandlers(logger, mockSys, config)

	req := httptest.NewRequest(http.MethodPost, "/debug/check-process", nil)
	rr := httptest.NewRecorder()

	h.HandleDebugCheckProcess(rr, req)

	if rr.Code != http.StatusMethodNotAllowed {
		t.Errorf("expected status %d, got %d", http.StatusMethodNotAllowed, rr.Code)
	}

	if !strings.Contains(rr.Body.String(), "Method not allowed") {
		t.Errorf("expected error message about method not allowed")
	}
}
