package handlers

import (
	"context"
	"io"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
	"time"

	"github.com/superfly/sprite-env/pkg/tap"
)

// Test NewHandlers constructor
func TestNewHandlers(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	config := Config{
		MaxWaitTime: 30 * time.Second,
	}
	mockSys := &mockSystemManager{}

	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	h := NewHandlers(ctx, mockSys, config)

	if h == nil {
		t.Error("NewHandlers returned nil")
	}
}

// Test HandleCheckpoint validates request method
func TestHandleCheckpointMethod(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	config := Config{}
	mockSys := newMockSystemManager()
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	h := NewHandlers(ctx, mockSys, config)

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
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	h := NewHandlers(ctx, mockSys, config)

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
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	h := NewHandlers(ctx, mockSys, config)

	// Test non-GET method (POST should fail)
	req := httptest.NewRequest(http.MethodPost, "/proxy", nil)
	rr := httptest.NewRecorder()

	h.HandleProxy(rr, req)

	if rr.Code != http.StatusMethodNotAllowed {
		t.Errorf("expected status %d, got %d", http.StatusMethodNotAllowed, rr.Code)
	}

	if !strings.Contains(rr.Body.String(), "Method not allowed") {
		t.Errorf("expected error message about method not allowed")
	}
}

// Test HandleProxy with GET method - will fail at WebSocket upgrade but method should be allowed
func TestHandleProxyGetMethod(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	config := Config{}
	mockSys := &mockSystemManager{}
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	h := NewHandlers(ctx, mockSys, config)

	req := httptest.NewRequest(http.MethodGet, "/proxy", nil)
	rr := httptest.NewRecorder()

	h.HandleProxy(rr, req)

	// Should not be method not allowed since GET is valid for WebSocket upgrade
	// Will fail at WebSocket upgrade since httptest.ResponseRecorder doesn't support it
	if rr.Code == http.StatusMethodNotAllowed {
		t.Errorf("GET should be allowed for WebSocket upgrade, got status %d", rr.Code)
	}
}

// Note: More comprehensive proxy tests that actually test WebSocket functionality
// would require a real HTTP server and WebSocket client, which is beyond the scope
// of these unit tests. The integration tests in proxy_simple_test.go should be
// updated to test the full WebSocket proxy functionality.

// Test HandleDebugCreateZombie validates request method
func TestHandleDebugCreateZombieMethod(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	config := Config{}
	mockSys := &mockSystemManager{}
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	h := NewHandlers(ctx, mockSys, config)

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
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	h := NewHandlers(ctx, mockSys, config)

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
