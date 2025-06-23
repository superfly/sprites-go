package handlers

import (
	"bytes"
	"context"
	"encoding/binary"
	"encoding/json"
	"fmt"
	"io"
	"lib/api"
	"lib/stdcopy"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"os"
	"sync"
	"testing"
	"time"

	"github.com/fly-dev-env/sprite-env/server/packages/juicefs"
)

// parseDockerMultiplexedStream parses a Docker multiplexed stream and returns stdout and stderr content
func parseDockerMultiplexedStream(data []byte) (stdout, stderr []byte, err error) {
	var stdoutBuf, stderrBuf bytes.Buffer
	reader := bytes.NewReader(data)

	for reader.Len() > 0 {
		// Read header (8 bytes)
		header := make([]byte, 8)
		n, err := reader.Read(header)
		if err != nil || n < 8 {
			break
		}

		// Parse header
		streamType := header[0]
		size := binary.BigEndian.Uint32(header[4:8])

		// Read payload
		payload := make([]byte, size)
		n, err = reader.Read(payload)
		if err != nil || n < int(size) {
			break
		}

		// Write to appropriate buffer
		switch streamType {
		case byte(stdcopy.Stdout):
			stdoutBuf.Write(payload)
		case byte(stdcopy.Stderr):
			stderrBuf.Write(payload)
		}
	}

	return stdoutBuf.Bytes(), stderrBuf.Bytes(), nil
}

// Test that Docker multiplexed format is compatible with moby/moby stdcopy
func TestDockerMultiplexedFormat(t *testing.T) {
	tests := []struct {
		name       string
		streamType stdcopy.StdType
		data       []byte
		expected   []byte
	}{
		{
			name:       "stdout message",
			streamType: stdcopy.Stdout,
			data:       []byte("Hello, stdout!"),
			expected: append(
				[]byte{byte(stdcopy.Stdout), 0, 0, 0, 0, 0, 0, 14}, // header: type=1, size=14
				[]byte("Hello, stdout!")...,                        // payload
			),
		},
		{
			name:       "stderr message",
			streamType: stdcopy.Stderr,
			data:       []byte("Error message"),
			expected: append(
				[]byte{byte(stdcopy.Stderr), 0, 0, 0, 0, 0, 0, 13}, // header: type=2, size=13
				[]byte("Error message")...,                         // payload
			),
		},
		{
			name:       "empty message",
			streamType: stdcopy.Stdout,
			data:       []byte{},
			expected:   []byte{byte(stdcopy.Stdout), 0, 0, 0, 0, 0, 0, 0}, // header: type=1, size=0
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			var buf bytes.Buffer
			writer := stdcopy.NewStdWriter(&buf, tt.streamType)
			_, err := writer.Write(tt.data)
			if err != nil {
				t.Fatalf("Write failed: %v", err)
			}
			if !bytes.Equal(buf.Bytes(), tt.expected) {
				t.Errorf("Expected %v, got %v", tt.expected, buf.Bytes())
			}
		})
	}
}

func TestDockerExecCreate(t *testing.T) {
	// Create handlers
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	mockSys := &testSystemManager{running: true}
	config := Config{}
	h := NewHandlers(logger, mockSys, config)

	// Test request
	req := api.DockerExecCreateRequest{
		Cmd:          []string{"ls", "-la"},
		AttachStdout: true,
		AttachStderr: true,
		Tty:          false,
	}

	body, _ := json.Marshal(req)
	r := httptest.NewRequest("POST", "/containers/test/exec", bytes.NewReader(body))
	w := httptest.NewRecorder()

	// Handle request
	h.HandleDockerExecCreate(w, r)

	// Check response
	if w.Code != http.StatusCreated {
		t.Errorf("Expected status 201, got %d", w.Code)
	}

	// Parse response
	var resp api.DockerExecCreateResponse
	if err := json.NewDecoder(w.Body).Decode(&resp); err != nil {
		t.Fatalf("Failed to decode response: %v", err)
	}

	if resp.Id == "" {
		t.Error("Expected exec ID in response")
	}

	// Check that instance was stored
	h.execMutex.RLock()
	instance, exists := h.execInstances[resp.Id]
	h.execMutex.RUnlock()

	if !exists {
		t.Error("Exec instance not stored")
	}

	if instance.Config.Cmd[0] != "ls" {
		t.Errorf("Expected command 'ls', got %s", instance.Config.Cmd[0])
	}
}

func TestDockerExecInspect(t *testing.T) {
	// Create handlers
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	mockSys := &testSystemManager{running: true}
	config := Config{}
	h := NewHandlers(logger, mockSys, config)

	// Create an exec instance
	instance := &ExecInstance{
		ID: "test-exec-id",
		Config: api.DockerExecCreateRequest{
			Cmd:          []string{"echo", "hello"},
			AttachStdout: true,
			AttachStderr: true,
			Tty:          false,
		},
		Running:     false,
		ExitCode:    0,
		ContainerID: defaultContainerID,
		Pid:         1234,
	}

	h.execMutex.Lock()
	h.execInstances["test-exec-id"] = instance
	h.execMutex.Unlock()

	// Test request
	r := httptest.NewRequest("GET", "/exec/test-exec-id/json", nil)
	w := httptest.NewRecorder()

	// Handle request
	h.HandleDockerExecInspect(w, r)

	// Check response
	if w.Code != http.StatusOK {
		t.Errorf("Expected status 200, got %d", w.Code)
	}

	// Parse response
	var resp api.DockerExecInspectResponse
	if err := json.NewDecoder(w.Body).Decode(&resp); err != nil {
		t.Fatalf("Failed to decode response: %v", err)
	}

	if resp.Id != "test-exec-id" {
		t.Errorf("Expected ID 'test-exec-id', got %s", resp.Id)
	}

	if resp.Running {
		t.Error("Expected Running to be false")
	}

	if resp.ExitCode != 0 {
		t.Errorf("Expected ExitCode 0, got %d", resp.ExitCode)
	}

	if resp.ProcessConfig.Entrypoint != "echo" {
		t.Errorf("Expected entrypoint 'echo', got %s", resp.ProcessConfig.Entrypoint)
	}
}

func TestDockerExecStart(t *testing.T) {
	// This test is more complex as it involves streaming
	// For now, we'll test the basic setup and error cases

	// Create handlers
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	mockSys := &testSystemManager{running: true}
	config := Config{}
	h := NewHandlers(logger, mockSys, config)

	// Test with non-existent exec ID
	req := api.DockerExecStartRequest{
		Detach: false,
		Tty:    false,
	}

	body, _ := json.Marshal(req)
	r := httptest.NewRequest("POST", "/exec/nonexistent/start", bytes.NewReader(body))
	w := httptest.NewRecorder()

	h.HandleDockerExecStart(w, r)

	if w.Code != http.StatusNotFound {
		t.Errorf("Expected status 404 for non-existent exec, got %d", w.Code)
	}

	// Test with detached mode - should now work
	instance := &ExecInstance{
		ID: "test-exec-id",
		Config: api.DockerExecCreateRequest{
			Cmd:          []string{"echo", "hello"},
			AttachStdout: true,
			AttachStderr: true,
		},
	}

	h.execMutex.Lock()
	h.execInstances["test-exec-id"] = instance
	h.execMutex.Unlock()

	req.Detach = true
	body, _ = json.Marshal(req)
	r = httptest.NewRequest("POST", "/exec/test-exec-id/start", bytes.NewReader(body))
	w = httptest.NewRecorder()

	h.HandleDockerExecStart(w, r)

	// Detached mode should return 200 OK
	if w.Code != http.StatusOK {
		t.Errorf("Expected status 200 for detached mode, got %d", w.Code)
	}

	// Wait a bit for the command to complete
	time.Sleep(100 * time.Millisecond)

	// Check that the instance was updated
	h.execMutex.RLock()
	updatedInstance := h.execInstances["test-exec-id"]
	h.execMutex.RUnlock()

	if updatedInstance.Running {
		t.Error("Expected Running to be false after command completes")
	}
}

// Helper to read all from a reader with timeout
func readWithTimeout(r io.Reader, timeout time.Duration) ([]byte, error) {
	ch := make(chan []byte, 1)
	errCh := make(chan error, 1)

	go func() {
		data, err := io.ReadAll(r)
		if err != nil {
			errCh <- err
		} else {
			ch <- data
		}
	}()

	select {
	case data := <-ch:
		return data, nil
	case err := <-errCh:
		return nil, err
	case <-time.After(timeout):
		return nil, io.ErrUnexpectedEOF
	}
}

// testSystemManager for testing that implements the SystemManager interface
type testSystemManager struct {
	running       bool
	hasJuiceFS    bool
	reapedPIDs    map[int]time.Time
	reapListeners []chan int
	mu            sync.Mutex
}

func (m *testSystemManager) IsProcessRunning() bool {
	m.mu.Lock()
	defer m.mu.Unlock()
	return m.running
}

func (m *testSystemManager) StartProcess() error {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.running = true
	return nil
}

func (m *testSystemManager) StopProcess() error {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.running = false
	return nil
}

func (m *testSystemManager) ForwardSignal(sig os.Signal) error {
	return nil
}

func (m *testSystemManager) HasJuiceFS() bool {
	m.mu.Lock()
	defer m.mu.Unlock()
	return m.hasJuiceFS
}

func (m *testSystemManager) CheckpointWithStream(ctx context.Context, checkpointID string, streamCh chan<- api.StreamMessage) error {
	defer close(streamCh)
	streamCh <- api.StreamMessage{
		Type: "info",
		Data: "Mock checkpoint created",
		Time: time.Now(),
	}
	return nil
}

func (m *testSystemManager) RestoreWithStream(ctx context.Context, checkpointID string, streamCh chan<- api.StreamMessage) error {
	defer close(streamCh)
	streamCh <- api.StreamMessage{
		Type: "info",
		Data: "Mock restore completed",
		Time: time.Now(),
	}
	return nil
}

func (m *testSystemManager) ListCheckpoints(ctx context.Context) ([]juicefs.CheckpointInfo, error) {
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

func (m *testSystemManager) GetCheckpoint(ctx context.Context, checkpointID string) (*juicefs.CheckpointInfo, error) {
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

func (m *testSystemManager) SubscribeToReapEvents() <-chan int {
	m.mu.Lock()
	defer m.mu.Unlock()
	ch := make(chan int, 10)
	m.reapListeners = append(m.reapListeners, ch)
	return ch
}

func (m *testSystemManager) UnsubscribeFromReapEvents(ch <-chan int) {
	m.mu.Lock()
	defer m.mu.Unlock()
	// Find and remove the channel
	for i, listener := range m.reapListeners {
		// Convert to comparable type
		if ch == (<-chan int)(listener) {
			m.reapListeners = append(m.reapListeners[:i], m.reapListeners[i+1:]...)
			close(listener)
			break
		}
	}
}

func (m *testSystemManager) WasProcessReaped(pid int) (bool, time.Time) {
	m.mu.Lock()
	defer m.mu.Unlock()
	if m.reapedPIDs == nil {
		m.reapedPIDs = make(map[int]time.Time)
	}
	t, exists := m.reapedPIDs[pid]
	return exists, t
}

func TestDockerStreamFormat(t *testing.T) {
	tests := []struct {
		name       string
		streamType stdcopy.StdType
		data       []byte
	}{
		{
			name:       "stdout message",
			streamType: stdcopy.Stdout,
			data:       []byte("Hello from stdout\n"),
		},
		{
			name:       "stderr message",
			streamType: stdcopy.Stderr,
			data:       []byte("Error from stderr\n"),
		},
		{
			name:       "empty message",
			streamType: stdcopy.Stdout,
			data:       []byte{},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			var buf bytes.Buffer
			writer := stdcopy.NewStdWriter(&buf, tt.streamType)
			_, err := writer.Write(tt.data)
			if err != nil {
				t.Fatalf("Write failed: %v", err)
			}

			// Verify the format
			result := buf.Bytes()
			if len(result) < 8 {
				t.Fatal("Output too short for Docker format")
			}

			// Check stream type
			if result[0] != byte(tt.streamType) {
				t.Errorf("Expected stream type %d, got %d", byte(tt.streamType), result[0])
			}

			// Check size
			size := uint32(result[4])<<24 | uint32(result[5])<<16 | uint32(result[6])<<8 | uint32(result[7])
			if size != uint32(len(tt.data)) {
				t.Errorf("Expected size %d, got %d", len(tt.data), size)
			}

			// Check payload
			payload := result[8:]
			if !bytes.Equal(payload, tt.data) {
				t.Errorf("Expected payload %q, got %q", tt.data, payload)
			}
		})
	}
}
