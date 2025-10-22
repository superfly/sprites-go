package api

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
	"github.com/superfly/sprite-env/pkg/services"
	"github.com/superfly/sprite-env/pkg/tap"
	"github.com/superfly/sprite-env/pkg/tmux"
)

// mockSystemManager implements SystemManager for testing
type mockSystemManager struct {
	isRunning       bool
	reapedProcesses map[int]time.Time
	reapListeners   []chan int
	existing        map[string]bool
}

func newMockSystemManager() *mockSystemManager {
	return &mockSystemManager{
		isRunning:       true,
		reapedProcesses: make(map[int]time.Time),
		reapListeners:   make([]chan int, 0),
		existing:        map[string]bool{"v0": true, "v1": true},
	}
}

func (m *mockSystemManager) GetTMUXManager() *tmux.Manager {
	return tmux.NewManager(context.Background(), tmux.Options{TmuxBinary: "/bin/echo"})
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

func (m *mockSystemManager) ListCheckpoints(ctx context.Context) ([]api.CheckpointInfo, error) {
	// Return mock checkpoints
	out := []api.CheckpointInfo{}
	if m.existing["v0"] {
		out = append(out, api.CheckpointInfo{ID: "v0", CreateTime: time.Now().Add(-2 * time.Hour)})
	}
	if m.existing["v1"] {
		out = append(out, api.CheckpointInfo{ID: "v1", CreateTime: time.Now().Add(-1 * time.Hour)})
	}
	return out, nil
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

func (m *mockSystemManager) GetCheckpoint(ctx context.Context, checkpointID string) (*api.CheckpointInfo, error) {
	// Return mock checkpoint
	if checkpointID == "v0" && m.existing["v0"] {
		return &api.CheckpointInfo{
			ID:         "v0",
			CreateTime: time.Now().Add(-2 * time.Hour),
			SourceID:   "",
		}, nil
	}
	if checkpointID == "v1" && m.existing["v1"] {
		return &api.CheckpointInfo{
			ID:         "v1",
			CreateTime: time.Now().Add(-1 * time.Hour),
			SourceID:   "",
		}, nil
	}
	return nil, fmt.Errorf("checkpoint %s does not exist", checkpointID)
}

func (m *mockSystemManager) DeleteCheckpoint(ctx context.Context, checkpointID string) error {
	if checkpointID == "active" || checkpointID == "Current" {
		return fmt.Errorf("cannot delete active checkpoint")
	}
	if _, ok := m.existing[checkpointID]; !ok || !m.existing[checkpointID] {
		return fmt.Errorf("not found")
	}
	m.existing[checkpointID] = false
	return nil
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

func (m *mockSystemManager) WhenProcessRunning(ctx context.Context) error {
	// Mock always returns immediately as if process is running
	return nil
}

func (m *mockSystemManager) WhenStorageReady(ctx context.Context) error {
	// Mock always returns immediately as if storage is ready
	return nil
}

func (m *mockSystemManager) SyncOverlay(ctx context.Context) (func() error, error) {
	return func() error { return nil }, nil
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

func (m *mockSystemManager) GetServicesManager() *services.Manager {
	return nil
}

func (m *mockSystemManager) GetLogDir() string {
	return "/tmp/test-logs"
}

func (m *mockSystemManager) SetSpriteEnvironment(ctx context.Context, info interface{}) (interface{}, error) {
	// Mock implementation returns a simple success response
	return map[string]string{
		"status":  "ok",
		"message": "Mock sprite environment set",
	}, nil
}

// TestHandleDebugCreateZombie tests the debug zombie creation handler
func TestHandleDebugCreateZombie(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	config := HandlerConfig{}
	mockSys := newMockSystemManager()
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
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	config := HandlerConfig{}
	mockSys := newMockSystemManager()
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
