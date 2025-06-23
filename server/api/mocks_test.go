package api

import (
	"context"
	"errors"
	"fmt"
	"io"
	"lib/api"
	"os"
	"sync"
	"time"

	"github.com/fly-dev-env/sprite-env/server/packages/juicefs"
)

// mockSupervisor implements Supervisor interface for testing
type mockSupervisor struct {
	mu         sync.Mutex
	pid        int
	running    bool
	startFunc  func() (int, error)
	stopFunc   func() error
	signalFunc func(sig os.Signal) error
	waitFunc   func() error
	startErr   error
	stopErr    error
	signalErr  error
	waitErr    error
}

func (m *mockSupervisor) Start() (int, error) {
	m.mu.Lock()
	defer m.mu.Unlock()

	if m.startFunc != nil {
		return m.startFunc()
	}
	if m.startErr != nil {
		return 0, m.startErr
	}
	m.running = true
	m.pid = 12345
	return m.pid, nil
}

func (m *mockSupervisor) Stop() error {
	m.mu.Lock()
	defer m.mu.Unlock()

	if m.stopFunc != nil {
		return m.stopFunc()
	}
	if m.stopErr != nil {
		return m.stopErr
	}
	m.running = false
	return nil
}

func (m *mockSupervisor) Signal(sig os.Signal) error {
	if m.signalFunc != nil {
		return m.signalFunc(sig)
	}
	if m.signalErr != nil {
		return m.signalErr
	}
	return nil
}

func (m *mockSupervisor) Wait() error {
	if m.waitFunc != nil {
		return m.waitFunc()
	}
	if m.waitErr != nil {
		return m.waitErr
	}
	m.running = false
	return nil
}

func (m *mockSupervisor) Pid() (int, error) {
	m.mu.Lock()
	defer m.mu.Unlock()

	if !m.running {
		return -1, errors.New("process not running")
	}
	return m.pid, nil
}

func (m *mockSupervisor) StdoutPipe() (io.ReadCloser, error) {
	return io.NopCloser(nil), nil
}

func (m *mockSupervisor) StderrPipe() (io.ReadCloser, error) {
	return io.NopCloser(nil), nil
}

// mockSystemManager implements handlers.SystemManager interface for testing
type mockSystemManager struct {
	mu              sync.Mutex
	processRunning  bool
	hasJuiceFS      bool
	reapedProcesses map[int]time.Time
	reapListeners   []chan int
}

func newMockSystemManager() *mockSystemManager {
	return &mockSystemManager{
		processRunning:  false,
		hasJuiceFS:      true,
		reapedProcesses: make(map[int]time.Time),
		reapListeners:   make([]chan int, 0),
	}
}

func (m *mockSystemManager) IsProcessRunning() bool {
	m.mu.Lock()
	defer m.mu.Unlock()
	return m.processRunning
}

func (m *mockSystemManager) StartProcess() error {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.processRunning = true
	return nil
}

func (m *mockSystemManager) StopProcess() error {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.processRunning = false
	return nil
}

func (m *mockSystemManager) ForwardSignal(sig os.Signal) error {
	return nil
}

func (m *mockSystemManager) HasJuiceFS() bool {
	m.mu.Lock()
	defer m.mu.Unlock()
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
		{
			ID:         "v2",
			CreateTime: time.Now().Add(-30 * time.Minute),
			SourceID:   "",
		},
	}, nil
}

func (m *mockSystemManager) ListCheckpointsByHistory(ctx context.Context, version string) ([]string, error) {
	// Return mock history search results
	if version == "v0" {
		return []string{
			"v1/.history: from=v0;time=2024-01-15T10:00:00Z",
			"v2/.history: from=v0;time=2024-01-15T11:00:00Z",
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
	if checkpointID == "v2" {
		return &juicefs.CheckpointInfo{
			ID:         "v2",
			CreateTime: time.Now().Add(-30 * time.Minute),
			SourceID:   "",
		}, nil
	}
	return nil, fmt.Errorf("checkpoint %s does not exist", checkpointID)
}

func (m *mockSystemManager) SubscribeToReapEvents() <-chan int {
	m.mu.Lock()
	defer m.mu.Unlock()
	ch := make(chan int, 10)
	m.reapListeners = append(m.reapListeners, ch)
	return ch
}

func (m *mockSystemManager) UnsubscribeFromReapEvents(ch <-chan int) {
	m.mu.Lock()
	defer m.mu.Unlock()
	for i, listener := range m.reapListeners {
		if listener == ch {
			close(listener)
			m.reapListeners = append(m.reapListeners[:i], m.reapListeners[i+1:]...)
			break
		}
	}
}

func (m *mockSystemManager) WasProcessReaped(pid int) (bool, time.Time) {
	m.mu.Lock()
	defer m.mu.Unlock()
	if reapTime, ok := m.reapedProcesses[pid]; ok {
		return true, reapTime
	}
	return false, time.Time{}
}

func (m *mockSystemManager) setProcessRunning(running bool) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.processRunning = running
}
