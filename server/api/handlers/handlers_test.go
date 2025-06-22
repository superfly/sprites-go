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

// Test that CommandType constants are properly defined
func TestCommandType(t *testing.T) {
	// Just test that the constants are defined and have unique values
	if CommandCheckpoint == CommandRestore {
		t.Error("CommandCheckpoint and CommandRestore should have different values")
	}

	if CommandCheckpoint == CommandExec {
		t.Error("CommandCheckpoint and CommandExec should have different values")
	}

	if CommandRestore == CommandExec {
		t.Error("CommandRestore and CommandExec should have different values")
	}

	// Test that they have the expected values based on iota
	if CommandExec != 0 {
		t.Errorf("CommandExec should be 0, got %d", CommandExec)
	}

	if CommandCheckpoint != 1 {
		t.Errorf("CommandCheckpoint should be 1, got %d", CommandCheckpoint)
	}

	if CommandRestore != 2 {
		t.Errorf("CommandRestore should be 2, got %d", CommandRestore)
	}
}

// Test NewHandlers constructor
func TestNewHandlers(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	commandCh := make(chan Command, 1)
	config := Config{
		MaxWaitTime: 30 * time.Second,
	}
	mockPM := &mockProcessManager{}

	h := NewHandlers(logger, commandCh, config, mockPM)

	if h == nil {
		t.Error("NewHandlers returned nil")
	}
}

// Test HandleCheckpoint validates request method
func TestHandleCheckpointMethod(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	commandCh := make(chan Command, 1)
	config := Config{}
	mockPM := &mockProcessManager{}
	h := NewHandlers(logger, commandCh, config, mockPM)

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
	commandCh := make(chan Command, 1)
	config := Config{}
	mockPM := &mockProcessManager{}
	h := NewHandlers(logger, commandCh, config, mockPM)

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
	commandCh := make(chan Command, 1)
	config := Config{}
	mockPM := &mockProcessManager{}
	h := NewHandlers(logger, commandCh, config, mockPM)

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
	commandCh := make(chan Command, 1)
	config := Config{}
	mockPM := &mockProcessManager{}
	h := NewHandlers(logger, commandCh, config, mockPM)

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
	commandCh := make(chan Command, 1)
	config := Config{}
	mockPM := &mockProcessManager{}
	h := NewHandlers(logger, commandCh, config, mockPM)

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
	commandCh := make(chan Command, 1)
	config := Config{}
	mockPM := &mockProcessManager{}
	h := NewHandlers(logger, commandCh, config, mockPM)

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

// mockProcessManager for unit testing
type mockProcessManager struct {
	running  bool
	commands []Command
}

func (m *mockProcessManager) SendCommand(cmd Command) CommandResponse {
	m.commands = append(m.commands, cmd)
	return CommandResponse{Success: true}
}

func (m *mockProcessManager) IsProcessRunning() bool {
	return m.running
}

func (m *mockProcessManager) SubscribeToReapEvents() <-chan int {
	ch := make(chan int)
	close(ch) // Close immediately for testing
	return ch
}

func (m *mockProcessManager) UnsubscribeFromReapEvents(ch <-chan int) {
	// No-op for testing
}

func (m *mockProcessManager) WasProcessReaped(pid int) (bool, time.Time) {
	return false, time.Time{}
}
