package api

import (
	"errors"
	"io"
	"os"
	"sync"
	"time"

	"spritectl/api/handlers"
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

// mockProcessManager implements ProcessManager interface for testing
type mockProcessManager struct {
	mu               sync.Mutex
	processRunning   bool
	commands         []handlers.Command
	commandResponses map[handlers.CommandType]handlers.CommandResponse
}

func newMockProcessManager() *mockProcessManager {
	return &mockProcessManager{
		processRunning:   false,
		commands:         make([]handlers.Command, 0),
		commandResponses: make(map[handlers.CommandType]handlers.CommandResponse),
	}
}

func (m *mockProcessManager) SendCommand(cmd handlers.Command) handlers.CommandResponse {
	m.mu.Lock()
	defer m.mu.Unlock()

	m.commands = append(m.commands, cmd)

	// Send response based on command type
	if resp, ok := m.commandResponses[cmd.Type]; ok {
		return resp
	}

	// Default responses
	switch cmd.Type {
	case handlers.CommandGetStatus:
		return handlers.CommandResponse{
			Success: true,
			Data:    m.processRunning,
		}
	case handlers.CommandCheckpoint:
		return handlers.CommandResponse{
			Success: true,
		}
	case handlers.CommandRestore:
		return handlers.CommandResponse{
			Success: true,
		}
	default:
		return handlers.CommandResponse{
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

func (m *mockProcessManager) setProcessRunning(running bool) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.processRunning = running
}

func (m *mockProcessManager) setCommandResponse(cmdType handlers.CommandType, resp handlers.CommandResponse) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.commandResponses[cmdType] = resp
}

// Mock command handler for testing
type mockCommandHandler struct {
	receivedCommands []handlers.Command
	responses        map[handlers.CommandType]handlers.CommandResponse
}

func newMockCommandHandler() *mockCommandHandler {
	return &mockCommandHandler{
		receivedCommands: make([]handlers.Command, 0),
		responses:        make(map[handlers.CommandType]handlers.CommandResponse),
	}
}

func (h *mockCommandHandler) setResponse(cmdType handlers.CommandType, resp handlers.CommandResponse) {
	h.responses[cmdType] = resp
}

func (h *mockCommandHandler) handleCommand(cmd handlers.Command) {
	h.receivedCommands = append(h.receivedCommands, cmd)

	if resp, ok := h.responses[cmd.Type]; ok {
		cmd.Response <- resp
	} else {
		cmd.Response <- handlers.CommandResponse{
			Success: false,
			Error:   errors.New("no response configured"),
		}
	}
}
