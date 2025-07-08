package tests

import (
	"context"
	"fmt"
	"io"
	"log/slog"
	"net"
	"net/http"
	"net/http/httptest"
	"os"
	"strings"
	"testing"
	"time"

	"github.com/sprite-env/lib/api"
	"github.com/sprite-env/packages/juicefs"
	"github.com/sprite-env/server/api/handlers"
	"github.com/superfly/sprite-env/pkg/terminal"
)

// TestProxyHandlerDirect tests the proxy handler directly
func TestProxyHandlerDirect(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	// Create a simple TCP echo server for testing
	listener, err := net.Listen("tcp", "localhost:0")
	if err != nil {
		t.Fatalf("Failed to create test server: %v", err)
	}
	defer listener.Close()

	// Get the port number
	port := listener.Addr().(*net.TCPAddr).Port

	// Start echo server
	go func() {
		for {
			conn, err := listener.Accept()
			if err != nil {
				return // Server closed
			}
			go func(c net.Conn) {
				defer c.Close()
				// Simple echo - read one message and echo it back
				buf := make([]byte, 1024)
				n, err := c.Read(buf)
				if err != nil {
					return
				}
				c.Write(buf[:n])
			}(conn)
		}
	}()

	// Create handlers
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	mockSys := &simpleSystemManager{}
	config := handlers.Config{}
	h := handlers.NewHandlers(logger, mockSys, config)

	t.Run("ValidCONNECTRequest", func(t *testing.T) {
		// Create a request that simulates a CONNECT request
		req := httptest.NewRequest(http.MethodConnect, "/proxy", nil)
		req.Host = fmt.Sprintf("localhost:%d", port)

		rr := httptest.NewRecorder()
		h.HandleProxy(rr, req)

		// The handler should return 200 OK for successful connection
		if rr.Code != http.StatusOK {
			t.Errorf("Expected status %d, got %d. Body: %s", http.StatusOK, rr.Code, rr.Body.String())
		}
	})

	t.Run("InvalidMethod", func(t *testing.T) {
		req := httptest.NewRequest(http.MethodGet, "/proxy", nil)
		req.Host = fmt.Sprintf("localhost:%d", port)

		rr := httptest.NewRecorder()
		h.HandleProxy(rr, req)

		if rr.Code != http.StatusMethodNotAllowed {
			t.Errorf("Expected status %d, got %d", http.StatusMethodNotAllowed, rr.Code)
		}
	})

	t.Run("InvalidHost", func(t *testing.T) {
		req := httptest.NewRequest(http.MethodConnect, "/proxy", nil)
		req.Host = "invalid-host" // No port

		rr := httptest.NewRecorder()
		h.HandleProxy(rr, req)

		if rr.Code != http.StatusBadRequest {
			t.Errorf("Expected status %d, got %d", http.StatusBadRequest, rr.Code)
		}

		if !strings.Contains(rr.Body.String(), "Invalid host format") {
			t.Errorf("Expected error about invalid host format, got: %s", rr.Body.String())
		}
	})

	t.Run("InvalidPort", func(t *testing.T) {
		req := httptest.NewRequest(http.MethodConnect, "/proxy", nil)
		req.Host = "localhost:99999" // Port too high

		rr := httptest.NewRecorder()
		h.HandleProxy(rr, req)

		if rr.Code != http.StatusBadRequest {
			t.Errorf("Expected status %d, got %d", http.StatusBadRequest, rr.Code)
		}

		if !strings.Contains(rr.Body.String(), "Invalid port number") {
			t.Errorf("Expected error about invalid port, got: %s", rr.Body.String())
		}
	})

	t.Run("ConnectionFailure", func(t *testing.T) {
		// Use a port that should be closed
		req := httptest.NewRequest(http.MethodConnect, "/proxy", nil)
		req.Host = "localhost:9999" // Unlikely to be open

		rr := httptest.NewRecorder()
		h.HandleProxy(rr, req)

		if rr.Code != http.StatusBadGateway {
			t.Errorf("Expected status %d, got %d", http.StatusBadGateway, rr.Code)
		}

		if !strings.Contains(rr.Body.String(), "Failed to connect to target") {
			t.Errorf("Expected error about connection failure, got: %s", rr.Body.String())
		}
	})
}

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

// simpleSystemManager for testing - minimal implementation
type simpleSystemManager struct{}

func (m *simpleSystemManager) IsProcessRunning() bool                          { return true }
func (m *simpleSystemManager) WaitForProcessRunning(ctx context.Context) error { return nil }
func (m *simpleSystemManager) StartProcess() error                             { return nil }
func (m *simpleSystemManager) StopProcess() error                              { return nil }
func (m *simpleSystemManager) ForwardSignal(sig os.Signal) error               { return nil }
func (m *simpleSystemManager) HasJuiceFS() bool                                { return false }
func (m *simpleSystemManager) WaitForJuiceFS(ctx context.Context) error        { return nil }
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
