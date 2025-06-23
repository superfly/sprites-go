package handlers

import (
	"context"
	"encoding/json"
	"fmt"
	"io"
	"lib/api"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"os"
	"testing"
	"time"

	"github.com/fly-dev-env/sprite-env/server/packages/juicefs"
)

// mockSystemManager implements SystemManager for testing
type mockSystemManager struct {
	isRunning       bool
	hasJuiceFS      bool
	reapedProcesses map[int]time.Time
	reapListeners   []chan int
}

func newMockSystemManager() *mockSystemManager {
	return &mockSystemManager{
		isRunning:       true,
		hasJuiceFS:      true,
		reapedProcesses: make(map[int]time.Time),
		reapListeners:   make([]chan int, 0),
	}
}

func (m *mockSystemManager) IsProcessRunning() bool {
	return m.isRunning
}

func (m *mockSystemManager) StartProcess() error {
	m.isRunning = true
	return nil
}

func (m *mockSystemManager) StopProcess() error {
	m.isRunning = false
	return nil
}

func (m *mockSystemManager) ForwardSignal(sig os.Signal) error {
	return nil
}

func (m *mockSystemManager) HasJuiceFS() bool {
	return m.hasJuiceFS
}

func (m *mockSystemManager) CheckpointWithStream(ctx context.Context, checkpointID string, streamCh chan<- api.StreamMessage) error {
	defer close(streamCh)
	streamCh <- api.StreamMessage{
		Type: "info",
		Data: "Mock checkpoint created",
		Time: time.Now(),
	}
	return nil
}

func (m *mockSystemManager) RestoreWithStream(ctx context.Context, checkpointID string, streamCh chan<- api.StreamMessage) error {
	defer close(streamCh)
	streamCh <- api.StreamMessage{
		Type: "info",
		Data: "Mock restore completed",
		Time: time.Now(),
	}
	return nil
}

func (m *mockSystemManager) ListCheckpoints(ctx context.Context) ([]juicefs.CheckpointInfo, error) {
	// Return mock checkpoints
	return []juicefs.CheckpointInfo{
		{
			ID:         "checkpoint-1",
			CreateTime: time.Now().Add(-1 * time.Hour),
			SourceID:   "",
		},
		{
			ID:         "checkpoint-2",
			CreateTime: time.Now().Add(-30 * time.Minute),
			SourceID:   "checkpoint-1",
		},
	}, nil
}

func (m *mockSystemManager) GetCheckpoint(ctx context.Context, checkpointID string) (*juicefs.CheckpointInfo, error) {
	// Return mock checkpoint
	if checkpointID == "checkpoint-1" {
		return &juicefs.CheckpointInfo{
			ID:         "checkpoint-1",
			CreateTime: time.Now().Add(-1 * time.Hour),
			SourceID:   "",
		}, nil
	}
	if checkpointID == "checkpoint-2" {
		return &juicefs.CheckpointInfo{
			ID:         "checkpoint-2",
			CreateTime: time.Now().Add(-30 * time.Minute),
			SourceID:   "checkpoint-1",
		}, nil
	}
	return nil, fmt.Errorf("checkpoint %s does not exist", checkpointID)
}

func (m *mockSystemManager) SubscribeToReapEvents() <-chan int {
	ch := make(chan int, 10)
	m.reapListeners = append(m.reapListeners, ch)
	return ch
}

func (m *mockSystemManager) UnsubscribeFromReapEvents(ch <-chan int) {
	for i, listener := range m.reapListeners {
		if listener == ch {
			close(listener)
			m.reapListeners = append(m.reapListeners[:i], m.reapListeners[i+1:]...)
			break
		}
	}
}

func (m *mockSystemManager) WasProcessReaped(pid int) (bool, time.Time) {
	if reapTime, ok := m.reapedProcesses[pid]; ok {
		return true, reapTime
	}
	return false, time.Time{}
}

// TestHandleDebugCreateZombie tests the debug zombie creation handler
func TestHandleDebugCreateZombie(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	config := Config{}
	mockSys := newMockSystemManager()
	h := NewHandlers(logger, mockSys, config)

	tests := []struct {
		name           string
		method         string
		expectedStatus int
	}{
		{
			name:           "POST method creates zombie",
			method:         http.MethodPost,
			expectedStatus: http.StatusOK,
		},
		{
			name:           "GET method not allowed",
			method:         http.MethodGet,
			expectedStatus: http.StatusMethodNotAllowed,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			req := httptest.NewRequest(tt.method, "/debug/create-zombie", nil)
			rr := httptest.NewRecorder()

			h.HandleDebugCreateZombie(rr, req)

			if rr.Code != tt.expectedStatus {
				t.Errorf("expected status %d, got %d", tt.expectedStatus, rr.Code)
			}

			// For successful requests, verify response format
			if tt.expectedStatus == http.StatusOK {
				var result map[string]interface{}
				if err := json.NewDecoder(rr.Body).Decode(&result); err != nil {
					t.Fatalf("Failed to decode response: %v", err)
				}

				// Check required fields
				requiredFields := []string{"message", "pid", "note"}
				for _, field := range requiredFields {
					if _, ok := result[field]; !ok {
						t.Errorf("Response missing required field: %s", field)
					}
				}
			}
		})
	}
}

// TestHandleDebugCheckProcess tests the debug process check handler
func TestHandleDebugCheckProcess(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	config := Config{}
	mockSys := newMockSystemManager()
	h := NewHandlers(logger, mockSys, config)

	tests := []struct {
		name           string
		method         string
		queryParams    string
		expectedStatus int
	}{
		{
			name:           "Valid PID",
			method:         http.MethodGet,
			queryParams:    "?pid=1",
			expectedStatus: http.StatusOK,
		},
		{
			name:           "Missing PID",
			method:         http.MethodGet,
			queryParams:    "",
			expectedStatus: http.StatusBadRequest,
		},
		{
			name:           "Invalid PID format",
			method:         http.MethodGet,
			queryParams:    "?pid=invalid",
			expectedStatus: http.StatusBadRequest,
		},
		{
			name:           "POST method not allowed",
			method:         http.MethodPost,
			queryParams:    "?pid=1",
			expectedStatus: http.StatusMethodNotAllowed,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			req := httptest.NewRequest(tt.method, "/debug/check-process"+tt.queryParams, nil)
			rr := httptest.NewRecorder()

			h.HandleDebugCheckProcess(rr, req)

			if rr.Code != tt.expectedStatus {
				t.Errorf("expected status %d, got %d", tt.expectedStatus, rr.Code)
			}

			// For successful requests, verify response format
			if tt.expectedStatus == http.StatusOK {
				var result map[string]interface{}
				if err := json.NewDecoder(rr.Body).Decode(&result); err != nil {
					t.Fatalf("Failed to decode response: %v", err)
				}

				// Check required fields
				requiredFields := []string{"pid", "exists", "is_zombie"}
				for _, field := range requiredFields {
					if _, ok := result[field]; !ok {
						t.Errorf("Response missing required field: %s", field)
					}
				}
			}
		})
	}
}
