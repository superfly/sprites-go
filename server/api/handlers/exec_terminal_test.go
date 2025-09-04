package handlers

import (
	"encoding/json"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"

	"github.com/superfly/sprite-env/pkg/terminal"
)

func TestHandleListExecSessions(t *testing.T) {
	// Create a test handler with a mock tmux manager
	logger := slog.Default()
	handlers := &Handlers{
		logger:      logger,
		tmuxManager: terminal.NewTMUXManager(logger),
	}

	// Create a test request
	req, err := http.NewRequest("GET", "/exec", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}

	// Create a response recorder
	w := httptest.NewRecorder()

	// Call the handler
	handlers.handleListExecSessions(w, req)

	// Check response status
	if w.Code != http.StatusOK {
		t.Errorf("Expected status OK, got %d", w.Code)
	}

	// Check content type
	contentType := w.Header().Get("Content-Type")
	if contentType != "application/json" {
		t.Errorf("Expected Content-Type application/json, got %s", contentType)
	}

	// Parse response body
	var response map[string]interface{}
	if err := json.Unmarshal(w.Body.Bytes(), &response); err != nil {
		t.Fatalf("Failed to unmarshal response: %v", err)
	}

	// Check response structure
	if _, ok := response["sessions"]; !ok {
		t.Error("Response missing 'sessions' field")
	}
	if _, ok := response["count"]; !ok {
		t.Error("Response missing 'count' field")
	}

	// Check that count is a number
	count, ok := response["count"].(float64)
	if !ok {
		t.Error("Count field is not a number")
	}

	// Check that sessions is an array
	sessions, ok := response["sessions"].([]interface{})
	if !ok {
		t.Error("Sessions field is not an array")
	}

	// Verify count matches sessions length
	if int(count) != len(sessions) {
		t.Errorf("Count %v doesn't match sessions length %d", count, len(sessions))
	}
}

func TestHandleListExecSessionsNoTMUXManager(t *testing.T) {
	// Create a test handler without tmux manager
	logger := slog.Default()
	handlers := &Handlers{
		logger:      logger,
		tmuxManager: nil,
	}

	// Create a test request
	req, err := http.NewRequest("GET", "/exec", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}

	// Create a response recorder
	w := httptest.NewRecorder()

	// Call the handler
	handlers.handleListExecSessions(w, req)

	// Check response status - should be 200 OK even when TMUXManager is not configured
	if w.Code != http.StatusOK {
		t.Errorf("Expected status 200 OK, got %d", w.Code)
	}

	// Parse JSON response
	var response map[string]interface{}
	if err := json.Unmarshal(w.Body.Bytes(), &response); err != nil {
		t.Fatalf("Failed to parse JSON response: %v", err)
	}

	// Check that sessions is empty
	sessions, ok := response["sessions"].([]interface{})
	if !ok {
		t.Errorf("Expected 'sessions' to be an array, got %T", response["sessions"])
	}
	if len(sessions) != 0 {
		t.Errorf("Expected empty sessions array, got %d sessions", len(sessions))
	}

	// Check count is 0
	count, ok := response["count"].(float64)
	if !ok {
		t.Errorf("Expected 'count' to be a number, got %T", response["count"])
	}
	if count != 0 {
		t.Errorf("Expected count to be 0, got %v", count)
	}

	// Check error message
	errorMsg, ok := response["error"].(string)
	if !ok {
		t.Errorf("Expected 'error' to be a string, got %T", response["error"])
	}
	if errorMsg != "TMUXManager not configured" {
		t.Errorf("Expected error message 'TMUXManager not configured', got '%s'", errorMsg)
	}
}

func TestHandleExecWebSocketUpgrade(t *testing.T) {
	// Create a test handler
	logger := slog.Default()
	handlers := &Handlers{
		logger:      logger,
		tmuxManager: terminal.NewTMUXManager(logger),
	}

	// Create a test request with WebSocket upgrade header
	req, err := http.NewRequest("GET", "/exec?cmd=echo&cmd=hello", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}
	req.Header.Set("Upgrade", "websocket")
	req.Header.Set("Connection", "upgrade")

	// Create a response recorder
	w := httptest.NewRecorder()

	// Call the handler
	handlers.HandleExec(w, req)

	// The WebSocket handler will try to upgrade the connection
	// We can't easily test the full WebSocket flow in a unit test,
	// but we can verify that it doesn't return a BadRequest error for valid requests
	// Note: The WebSocket library will return an error about missing WebSocket protocol,
	// but this is expected in a test environment
	if w.Code == http.StatusBadRequest && strings.Contains(w.Body.String(), "No command specified") {
		t.Errorf("Expected no BadRequest error for WebSocket upgrade, got %d: %s", w.Code, w.Body.String())
	}
}

func TestHandleExecListSessions(t *testing.T) {
	// Create a test handler
	logger := slog.Default()
	handlers := &Handlers{
		logger:      logger,
		tmuxManager: terminal.NewTMUXManager(logger),
	}

	// Create a test request without WebSocket upgrade header
	req, err := http.NewRequest("GET", "/exec", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}

	// Create a response recorder
	w := httptest.NewRecorder()

	// Call the handler
	handlers.HandleExec(w, req)

	// Should return list of sessions
	if w.Code != http.StatusOK {
		t.Errorf("Expected status OK, got %d", w.Code)
	}

	// Check content type
	contentType := w.Header().Get("Content-Type")
	if contentType != "application/json" {
		t.Errorf("Expected Content-Type application/json, got %s", contentType)
	}
}

func TestHandleExecPOSTNotAllowed(t *testing.T) {
	// Create a test handler
	logger := slog.Default()
	handlers := &Handlers{
		logger:      logger,
		tmuxManager: terminal.NewTMUXManager(logger),
	}

	// Create a test POST request (should be rejected regardless of content)
	req, err := http.NewRequest("POST", "/exec", strings.NewReader("{}"))
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}

	// Create a response recorder
	w := httptest.NewRecorder()

	// Call the handler
	handlers.HandleExec(w, req)

	// Should return MethodNotAllowed for POST
	if w.Code != http.StatusMethodNotAllowed {
		t.Errorf("Expected status MethodNotAllowed (405), got %d", w.Code)
	}

	// Check error message
	body := strings.TrimSpace(w.Body.String())
	expected := "Method not allowed"
	if body != expected {
		t.Errorf("Expected error message '%s', got '%s'", expected, body)
	}
}
