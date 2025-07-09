package tests

import (
	"context"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"os"
	"testing"
	"time"

	"github.com/sprite-env/lib/api"
	"github.com/sprite-env/packages/juicefs"
	"github.com/sprite-env/server/api/handlers"
	"github.com/superfly/sprite-env/pkg/terminal"
)

// Note: These proxy tests were designed for the old HTTP CONNECT approach.
// They need to be rewritten to test the new WebSocket-based proxy functionality.
// For now, we'll skip the complex connection tests and only test basic validation.

// TestProxyHandlerDirect tests the proxy handler directly
func TestProxyHandlerDirect(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	// Create handlers
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	mockSys := &simpleSystemManager{}
	config := handlers.Config{}
	h := handlers.NewHandlers(logger, mockSys, config)

	t.Run("MethodValidation", func(t *testing.T) {
		// Test that POST method is not allowed (should be GET for WebSocket)
		req := httptest.NewRequest(http.MethodPost, "/proxy", nil)
		rr := httptest.NewRecorder()
		h.HandleProxy(rr, req)

		if rr.Code != http.StatusMethodNotAllowed {
			t.Errorf("Expected status %d, got %d", http.StatusMethodNotAllowed, rr.Code)
		}
	})

	t.Run("GetMethodAllowed", func(t *testing.T) {
		// Test that GET method is allowed (for WebSocket upgrade)
		req := httptest.NewRequest(http.MethodGet, "/proxy", nil)
		rr := httptest.NewRecorder()
		h.HandleProxy(rr, req)

		// Should not return method not allowed
		if rr.Code == http.StatusMethodNotAllowed {
			t.Errorf("GET method should be allowed for WebSocket upgrade")
		}
	})

	// TODO: Add comprehensive WebSocket proxy tests
	// These would require setting up actual WebSocket connections and are more complex
	// than the old HTTP CONNECT tests. They should test:
	// 1. WebSocket upgrade
	// 2. Initial JSON message with target host:port
	// 3. Binary data forwarding between WebSocket and TCP
	// 4. Error handling for invalid JSON, bad ports, connection failures
	// 5. Authentication via WebSocket headers
}

// The following tests are commented out because they were designed for HTTP CONNECT
// and need to be rewritten for the new WebSocket-based proxy approach.

/*
// TestProxyWithAuthentication tests proxy with authentication middleware
func TestProxyWithAuthentication(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	// Create a test server that accepts connections
	listener, err := net.Listen("tcp", "localhost:0")
	if err != nil {
		t.Fatalf("Failed to create test server: %v", err)
	}
	defer listener.Close()

	port := listener.Addr().(*net.TCPAddr).Port

	// Start a simple server that accepts connections
	go func() {
		for {
			conn, err := listener.Accept()
			if err != nil {
				return
			}
			conn.Close() // Just accept and close
		}
	}()

	// Create handlers with auth
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	mockSys := &simpleSystemManager{}
	config := handlers.Config{}
	h := handlers.NewHandlers(logger, mockSys, config)

	// Create auth middleware
	apiToken := "test-token-123"
	authMiddleware := func(next http.HandlerFunc) http.HandlerFunc {
		return func(w http.ResponseWriter, r *http.Request) {
			authHeader := r.Header.Get("Authorization")
			if authHeader == "" {
				http.Error(w, "Missing authentication", http.StatusUnauthorized)
				return
			}

			parts := strings.SplitN(authHeader, " ", 2)
			if len(parts) != 2 || strings.ToLower(parts[0]) != "bearer" || parts[1] != apiToken {
				http.Error(w, "Invalid authentication token", http.StatusUnauthorized)
				return
			}

			next(w, r)
		}
	}

	t.Run("ValidAuth", func(t *testing.T) {
		req := httptest.NewRequest(http.MethodConnect, "/proxy", nil)
		req.Host = fmt.Sprintf("localhost:%d", port)
		req.Header.Set("Authorization", "Bearer "+apiToken)

		rr := httptest.NewRecorder()
		authMiddleware(h.HandleProxy)(rr, req)

		if rr.Code != http.StatusOK {
			t.Errorf("Expected status %d, got %d. Body: %s", http.StatusOK, rr.Code, rr.Body.String())
		}
	})

	t.Run("InvalidAuth", func(t *testing.T) {
		req := httptest.NewRequest(http.MethodConnect, "/proxy", nil)
		req.Host = fmt.Sprintf("localhost:%d", port)
		req.Header.Set("Authorization", "Bearer wrong-token")

		rr := httptest.NewRecorder()
		authMiddleware(h.HandleProxy)(rr, req)

		if rr.Code != http.StatusUnauthorized {
			t.Errorf("Expected status %d, got %d", http.StatusUnauthorized, rr.Code)
		}
	})

	t.Run("MissingAuth", func(t *testing.T) {
		req := httptest.NewRequest(http.MethodConnect, "/proxy", nil)
		req.Host = fmt.Sprintf("localhost:%d", port)

		rr := httptest.NewRecorder()
		authMiddleware(h.HandleProxy)(rr, req)

		if rr.Code != http.StatusUnauthorized {
			t.Errorf("Expected status %d, got %d", http.StatusUnauthorized, rr.Code)
		}
	})
}

/*
// TestProxyPortParsing tests various port parsing scenarios
func TestProxyPortParsing(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	mockSys := &simpleSystemManager{}
	config := handlers.Config{}
	h := handlers.NewHandlers(logger, mockSys, config)

	tests := []struct {
		name         string
		host         string
		expectedCode int
		expectedMsg  string
	}{
		{
			name:         "Valid port",
			host:         "localhost:8080",
			expectedCode: http.StatusBadGateway, // Will fail to connect but port is valid
			expectedMsg:  "Failed to connect to target",
		},
		{
			name:         "Port 1",
			host:         "localhost:1",
			expectedCode: http.StatusBadGateway,
			expectedMsg:  "Failed to connect to target",
		},
		{
			name:         "Port 65535",
			host:         "localhost:65535",
			expectedCode: http.StatusBadGateway,
			expectedMsg:  "Failed to connect to target",
		},
		{
			name:         "Port 0",
			host:         "localhost:0",
			expectedCode: http.StatusBadRequest,
			expectedMsg:  "Invalid port number",
		},
		{
			name:         "Port too high",
			host:         "localhost:65536",
			expectedCode: http.StatusBadRequest,
			expectedMsg:  "Invalid port number",
		},
		{
			name:         "Negative port",
			host:         "localhost:-1",
			expectedCode: http.StatusBadRequest,
			expectedMsg:  "Invalid port number",
		},
		{
			name:         "Non-numeric port",
			host:         "localhost:abc",
			expectedCode: http.StatusBadRequest,
			expectedMsg:  "Invalid port number",
		},
		{
			name:         "No port",
			host:         "localhost",
			expectedCode: http.StatusBadRequest,
			expectedMsg:  "Invalid host format",
		},
		{
			name:         "Multiple colons",
			host:         "localhost:8080:extra",
			expectedCode: http.StatusBadRequest,
			expectedMsg:  "Invalid host format",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			req := httptest.NewRequest(http.MethodConnect, "/proxy", nil)
			req.Host = tt.host

			rr := httptest.NewRecorder()
			h.HandleProxy(rr, req)

			if rr.Code != tt.expectedCode {
				t.Errorf("Expected status %d, got %d", tt.expectedCode, rr.Code)
			}

			if !strings.Contains(rr.Body.String(), tt.expectedMsg) {
				t.Errorf("Expected message containing '%s', got: %s", tt.expectedMsg, rr.Body.String())
			}
		})
	}
}
*/

// simpleSystemManager for testing - minimal implementation
type simpleSystemManager struct{}

func (m *simpleSystemManager) IsProcessRunning() bool                          { return true }
func (m *simpleSystemManager) WaitForProcessRunning(ctx context.Context) error { return nil }
func (m *simpleSystemManager) StartProcess() error                             { return nil }
func (m *simpleSystemManager) StopProcess() error                              { return nil }
func (m *simpleSystemManager) ForwardSignal(sig os.Signal) error               { return nil }
func (m *simpleSystemManager) MonitorExecProcess(execID string, execFunc func() error) error {
	return execFunc()
}
func (m *simpleSystemManager) StartExecProcessTracking(execID string, pid int) error { return nil }
func (m *simpleSystemManager) StopExecProcessTracking(execID string)                 {}
func (m *simpleSystemManager) HasJuiceFS() bool                                      { return false }
func (m *simpleSystemManager) WaitForJuiceFS(ctx context.Context) error              { return nil }
func (m *simpleSystemManager) CheckpointWithStream(ctx context.Context, checkpointID string, streamCh chan<- api.StreamMessage) error {
	defer close(streamCh)
	return nil
}
func (m *simpleSystemManager) RestoreWithStream(ctx context.Context, checkpointID string, streamCh chan<- api.StreamMessage) error {
	defer close(streamCh)
	return nil
}
func (m *simpleSystemManager) ListCheckpoints(ctx context.Context) ([]juicefs.CheckpointInfo, error) {
	return []juicefs.CheckpointInfo{}, nil
}
func (m *simpleSystemManager) ListCheckpointsByHistory(ctx context.Context, version string) ([]string, error) {
	return []string{}, nil
}
func (m *simpleSystemManager) GetCheckpoint(ctx context.Context, checkpointID string) (*juicefs.CheckpointInfo, error) {
	return nil, fmt.Errorf("checkpoint not found")
}
func (m *simpleSystemManager) SubscribeToReapEvents() <-chan int {
	return make(chan int)
}
func (m *simpleSystemManager) UnsubscribeFromReapEvents(ch <-chan int) {}
func (m *simpleSystemManager) WasProcessReaped(pid int) (bool, time.Time) {
	return false, time.Time{}
}
func (m *simpleSystemManager) EnableTranscripts(ctx context.Context) error {
	return nil
}
func (m *simpleSystemManager) DisableTranscripts(ctx context.Context) error {
	return nil
}
func (m *simpleSystemManager) IsTranscriptsEnabled() bool {
	return false
}
func (m *simpleSystemManager) CreateTranscriptCollector(env []string, ty bool) (terminal.TranscriptCollector, error) {
	return nil, nil
}
func (m *simpleSystemManager) IsConfigured() bool {
	return true
}
func (m *simpleSystemManager) Configure(config interface{}) error {
	return nil
}
func (m *simpleSystemManager) Boot(ctx context.Context) error {
	return nil
}
func (m *simpleSystemManager) GetDynamicConfigPath() string {
	return "/tmp/mock-config.json"
}
