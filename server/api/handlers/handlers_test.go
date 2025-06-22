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

// Test HandleRestore validates request method
func TestHandleRestoreMethod(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	config := Config{}
	mockSys := newMockSystemManager()
	h := NewHandlers(logger, mockSys, config)

	req := httptest.NewRequest(http.MethodGet, "/restore", nil)
	rr := httptest.NewRecorder()

	h.HandleRestore(rr, req)

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

// Test HandleProxy with CONNECT method returns not implemented
func TestHandleProxyNotImplemented(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	config := Config{}
	mockSys := &mockSystemManager{}
	h := NewHandlers(logger, mockSys, config)

	req := httptest.NewRequest(http.MethodConnect, "/proxy/example.com", nil)
	rr := httptest.NewRecorder()

	h.HandleProxy(rr, req)

	if rr.Code != http.StatusNotImplemented {
		t.Errorf("expected status %d, got %d", http.StatusNotImplemented, rr.Code)
	}

	if !strings.Contains(rr.Body.String(), "not yet implemented") {
		t.Errorf("expected error message about not implemented")
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
