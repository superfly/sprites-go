package api

import (
	"context"
	"errors"
	"io"
	"os"
	"sync"
)

// mockJuiceFS implements JuiceFS interface for testing
type mockJuiceFS struct {
	checkpointFunc func(ctx context.Context, checkpointID string) error
	restoreFunc    func(ctx context.Context, checkpointID string) error
}

func (m *mockJuiceFS) Checkpoint(ctx context.Context, checkpointID string) error {
	if m.checkpointFunc != nil {
		return m.checkpointFunc(ctx, checkpointID)
	}
	return nil
}

func (m *mockJuiceFS) Restore(ctx context.Context, checkpointID string) error {
	if m.restoreFunc != nil {
		return m.restoreFunc(ctx, checkpointID)
	}
	return nil
}

// mockSupervisor implements Supervisor interface for testing
type mockSupervisor struct {
	mu         sync.Mutex
	pid        int
	running    bool
	startFunc  func() (int, error)
	stopFunc   func() error
	signalFunc func(sig os.Signal) error
	waitFunc   func() error
}

func (m *mockSupervisor) Start() (int, error) {
	m.mu.Lock()
	defer m.mu.Unlock()

	if m.startFunc != nil {
		return m.startFunc()
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
	m.running = false
	return nil
}

func (m *mockSupervisor) Signal(sig os.Signal) error {
	if m.signalFunc != nil {
		return m.signalFunc(sig)
	}
	return nil
}

func (m *mockSupervisor) Wait() error {
	if m.waitFunc != nil {
		return m.waitFunc()
	}
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

// mockProcessManager implements ProcessManager interface for testing
type mockProcessManager struct {
	mu               sync.Mutex
	processRunning   bool
	commandResponses map[CommandType]CommandResponse
}

func newMockProcessManager() *mockProcessManager {
	return &mockProcessManager{
		commandResponses: make(map[CommandType]CommandResponse),
	}
}

func (m *mockProcessManager) SendCommand(cmd Command) CommandResponse {
	m.mu.Lock()
	defer m.mu.Unlock()

	// Send response based on command type
	if resp, ok := m.commandResponses[cmd.Type]; ok {
		return resp
	}

	// Default responses
	switch cmd.Type {
	case CommandGetStatus:
		return CommandResponse{
			Success: true,
			Data:    m.processRunning,
		}
	case CommandCheckpoint:
		return CommandResponse{
			Success: true,
		}
	case CommandRestore:
		return CommandResponse{
			Success: true,
		}
	default:
		return CommandResponse{
			Success: false,
			Error:   errors.New("unknown command"),
		}
	}
}

func (m *mockProcessManager) IsProcessRunning() bool {
	m.mu.Lock()
	defer m.mu.Unlock()
	return m.processRunning
}

func (m *mockProcessManager) setProcessRunning(running bool) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.processRunning = running
}

func (m *mockProcessManager) setCommandResponse(cmdType CommandType, resp CommandResponse) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.commandResponses[cmdType] = resp
}
