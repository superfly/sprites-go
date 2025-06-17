package state

import (
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
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

func TestCheckpointHandler(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))

	t.Run("successful checkpoint", func(t *testing.T) {
		mockState := &mockSystemState{}
		handler := NewHandler(mockState, logger)

		req := httptest.NewRequest("POST", "/checkpoint", strings.NewReader(`{
			"checkpoint_id": "test-checkpoint-123"
		}`))
		req.Header.Set("Content-Type", "application/json")

		rr := httptest.NewRecorder()
		handler.HandleCheckpoint(rr, req)

		if rr.Code != http.StatusAccepted {
			t.Errorf("expected status 202, got %d", rr.Code)
		}

		// Verify Fire was called correctly
		if len(mockState.fireCalls) != 1 {
			t.Fatalf("expected 1 Fire call, got %d", len(mockState.fireCalls))
		}

		call := mockState.fireCalls[0]
		if call.trigger != "CheckpointRequested" {
			t.Errorf("expected trigger CheckpointRequested, got %s", call.trigger)
		}
		if len(call.args) != 1 || call.args[0] != "test-checkpoint-123" {
			t.Errorf("expected checkpoint ID as argument, got %v", call.args)
		}

		// Check response body contains checkpoint ID
		if !strings.Contains(rr.Body.String(), "test-checkpoint-123") {
			t.Errorf("response should contain checkpoint ID")
		}
	})

	t.Run("Fire returns error", func(t *testing.T) {
		mockState := &mockSystemState{
			fireError: fmt.Errorf("invalid state transition"),
		}
		handler := NewHandler(mockState, logger)

		req := httptest.NewRequest("POST", "/checkpoint", strings.NewReader(`{
			"checkpoint_id": "test-checkpoint-123"
		}`))
		req.Header.Set("Content-Type", "application/json")

		rr := httptest.NewRecorder()
		handler.HandleCheckpoint(rr, req)

		if rr.Code != http.StatusInternalServerError {
			t.Errorf("expected status 500 when Fire fails, got %d", rr.Code)
		}

		// Error message should mention the failure
		if !strings.Contains(rr.Body.String(), "Failed to start checkpoint") {
			t.Errorf("expected error message about failed checkpoint, got: %s", rr.Body.String())
		}
		if !strings.Contains(rr.Body.String(), "invalid state transition") {
			t.Errorf("expected original error message in response, got: %s", rr.Body.String())
		}
	})

	t.Run("empty checkpoint ID", func(t *testing.T) {
		mockState := &mockSystemState{}
		handler := NewHandler(mockState, logger)

		req := httptest.NewRequest("POST", "/checkpoint", strings.NewReader(`{
			"checkpoint_id": ""
		}`))
		req.Header.Set("Content-Type", "application/json")

		rr := httptest.NewRecorder()
		handler.HandleCheckpoint(rr, req)

		if rr.Code != http.StatusBadRequest {
			t.Errorf("expected status 400 for empty checkpoint ID, got %d", rr.Code)
		}

		if !strings.Contains(rr.Body.String(), "checkpoint_id is required") {
			t.Errorf("unexpected error message: %s", rr.Body.String())
		}

		// Verify Fire was not called
		if len(mockState.fireCalls) != 0 {
			t.Errorf("Fire should not be called with empty checkpoint ID")
		}
	})

	t.Run("invalid method", func(t *testing.T) {
		mockState := &mockSystemState{}
		handler := NewHandler(mockState, logger)

		req := httptest.NewRequest("GET", "/checkpoint", nil)

		rr := httptest.NewRecorder()
		handler.HandleCheckpoint(rr, req)

		if rr.Code != http.StatusMethodNotAllowed {
			t.Errorf("expected status 405 for GET method, got %d", rr.Code)
		}
	})
}

func TestRestoreHandler(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))

	t.Run("successful restore", func(t *testing.T) {
		mockState := &mockSystemState{}
		handler := NewHandler(mockState, logger)

		req := httptest.NewRequest("POST", "/restore", strings.NewReader(`{
			"checkpoint_id": "test-checkpoint-123"
		}`))
		req.Header.Set("Content-Type", "application/json")

		rr := httptest.NewRecorder()
		handler.HandleRestore(rr, req)

		if rr.Code != http.StatusAccepted {
			t.Errorf("expected status 202, got %d", rr.Code)
		}

		// Verify Fire was called correctly
		if len(mockState.fireCalls) != 1 {
			t.Fatalf("expected 1 Fire call, got %d", len(mockState.fireCalls))
		}

		call := mockState.fireCalls[0]
		if call.trigger != "RestoreRequested" {
			t.Errorf("expected trigger RestoreRequested, got %s", call.trigger)
		}
		if len(call.args) != 1 || call.args[0] != "test-checkpoint-123" {
			t.Errorf("expected checkpoint ID as argument, got %v", call.args)
		}
	})

	t.Run("Fire returns error", func(t *testing.T) {
		mockState := &mockSystemState{
			fireError: fmt.Errorf("cannot restore in current state"),
		}
		handler := NewHandler(mockState, logger)

		req := httptest.NewRequest("POST", "/restore", strings.NewReader(`{
			"checkpoint_id": "test-checkpoint-123"
		}`))
		req.Header.Set("Content-Type", "application/json")

		rr := httptest.NewRecorder()
		handler.HandleRestore(rr, req)

		if rr.Code != http.StatusInternalServerError {
			t.Errorf("expected status 500 when Fire fails, got %d", rr.Code)
		}

		// Error message should mention the failure
		if !strings.Contains(rr.Body.String(), "Failed to start restore") {
			t.Errorf("expected error message about failed restore, got: %s", rr.Body.String())
		}
		if !strings.Contains(rr.Body.String(), "cannot restore in current state") {
			t.Errorf("expected original error message in response, got: %s", rr.Body.String())
		}
	})

	t.Run("missing checkpoint ID", func(t *testing.T) {
		mockState := &mockSystemState{}
		handler := NewHandler(mockState, logger)

		req := httptest.NewRequest("POST", "/restore", strings.NewReader(`{}`))
		req.Header.Set("Content-Type", "application/json")

		rr := httptest.NewRecorder()
		handler.HandleRestore(rr, req)

		if rr.Code != http.StatusBadRequest {
			t.Errorf("expected status 400 for missing checkpoint ID, got %d", rr.Code)
		}

		if !strings.Contains(rr.Body.String(), "checkpoint_id is required") {
			t.Errorf("unexpected error message: %s", rr.Body.String())
		}

		// Verify Fire was not called
		if len(mockState.fireCalls) != 0 {
			t.Errorf("Fire should not be called with missing checkpoint ID")
		}
	})
}
