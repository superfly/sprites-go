package handlers

import (
	"context"
	"encoding/json"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"os"
	"testing"
	"time"

	"github.com/superfly/sprite-env/lib/api"
	"github.com/superfly/sprite-env/pkg/tap"

	"github.com/superfly/sprite-env/pkg/juicefs"
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

// Exec process monitoring methods
func (m *mockSystemManager) MonitorExecProcess(execID string, execFunc func() error) error {
	// Mock implementation just calls the function
	return execFunc()
}

func (m *mockSystemManager) StartExecProcessTracking(execID string, pid int) error {
	// Mock implementation does nothing
	return nil
}

func (m *mockSystemManager) StopExecProcessTracking(execID string) {
	// Mock implementation does nothing
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
			ID:         "v0",
			CreateTime: time.Now().Add(-2 * time.Hour),
			SourceID:   "",
		},
		{
			ID:         "v1",
			CreateTime: time.Now().Add(-1 * time.Hour),
			SourceID:   "",
		},
	}, nil
}

func (m *mockSystemManager) ListCheckpointsByHistory(ctx context.Context, version string) ([]string, error) {
	// Return mock history search results
	if version == "v0" {
		return []string{
			"v1/.history: from=v0;time=2024-01-15T10:00:00Z",
		}, nil
	}
	return []string{}, nil
}

func (m *mockSystemManager) GetCheckpoint(ctx context.Context, checkpointID string) (*juicefs.CheckpointInfo, error) {
	// Return mock checkpoint
	if checkpointID == "v0" {
		return &juicefs.CheckpointInfo{
			ID:         "v0",
			CreateTime: time.Now().Add(-2 * time.Hour),
			SourceID:   "",
		}, nil
	}
	if checkpointID == "v1" {
		return &juicefs.CheckpointInfo{
			ID:         "v1",
			CreateTime: time.Now().Add(-1 * time.Hour),
			SourceID:   "",
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

func (m *mockSystemManager) WaitForProcessRunning(ctx context.Context) error {
	// Mock always returns immediately as if process is running
	return nil
}

func (m *mockSystemManager) WaitForJuiceFS(ctx context.Context) error {
	// Mock always returns immediately as if JuiceFS is ready
	return nil
}

func (m *mockSystemManager) SyncOverlay(ctx context.Context) error {
	return nil
}

func (m *mockSystemManager) Boot(ctx context.Context) error {
	return nil
}

func (m *mockSystemManager) Shutdown(ctx context.Context) error {
	return nil
}

func (m *mockSystemManager) Wait() error {
	return nil
}

func (m *mockSystemManager) ResolvePID(pid int) (int, error) {
	return pid, nil // Simple passthrough for tests
}

// TestHandleDebugCreateZombie tests the debug zombie creation handler
func TestHandleDebugCreateZombie(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	config := Config{}
	mockSys := newMockSystemManager()
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	h := NewHandlers(ctx, mockSys, config)

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
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	h := NewHandlers(ctx, mockSys, config)

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
