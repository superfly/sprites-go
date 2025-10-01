package services

import (
	"context"
	"fmt"
	"os"
	"time"

	"github.com/superfly/sprite-env/pkg/tap"
)

// Manager manages service lifecycle and dependencies
type Manager struct {
	db        *DB
	dataDir   string // Directory for database
	cmdPrefix []string
	logDir    string // Directory for service logs

	// Channel-based state management
	commands      chan command
	stateRequests chan stateRequest
	ctx           context.Context
	cancel        context.CancelFunc
}

// command represents an operation on the manager
type command struct {
	op       operation
	svc      *Service
	name     string
	signal   string           // for opSignal
	exitCode int              // for opProcessExit
	result   chan interface{} // can be error or other types like *ProcessHandle
}

type operation int

const (
	opCreate operation = iota
	opDelete
	opStart
	opStop
	opShutdown
	opProcessExit
	opSignal
	opStartAll
	opGetProcessHandle
)

type stateRequest struct {
	name   string
	result chan *ServiceState
}

// Option configures the Manager
type Option func(*Manager)

// WithLogDir sets the directory for service logs
func WithLogDir(logDir string) Option {
	return func(m *Manager) {
		m.logDir = logDir
	}
}

// NewManager creates a new service manager
func NewManager(dataDir string, opts ...Option) (*Manager, error) {
	ctx, cancel := context.WithCancel(context.Background())

	m := &Manager{
		dataDir:       dataDir,
		commands:      make(chan command),
		stateRequests: make(chan stateRequest),
		ctx:           ctx,
		cancel:        cancel,
	}

	// Apply options
	for _, opt := range opts {
		opt(m)
	}

	// Set up log directory if configured
	if m.logDir != "" {
		logDir := fmt.Sprintf("%s/services", m.logDir)
		if err := os.MkdirAll(logDir, 0755); err != nil {
			return nil, fmt.Errorf("failed to create log directory: %w", err)
		}
	}

	// Start the manager loop
	go m.run()

	return m, nil
}

// SetCmdPrefix sets the command prefix for service execution
func (m *Manager) SetCmdPrefix(prefix []string) {
	m.cmdPrefix = prefix
	tap.Logger(m.ctx).Info("Service manager command prefix has been set", "prefix", prefix)
}

// Start initializes the database and prepares the manager
func (m *Manager) Start() error {
	if m.db != nil {
		return nil // Already started
	}

	fmt.Printf("Starting services manager, initializing database in %s\n", m.dataDir)
	db, err := NewDB(m.dataDir)
	if err != nil {
		return fmt.Errorf("failed to create database: %w", err)
	}
	m.db = db

	tap.Logger(m.ctx).Info("Services manager started", "dataDir", m.dataDir)
	return nil
}

// ensureDB checks if the database is initialized
func (m *Manager) ensureDB() error {
	if m.db == nil {
		return fmt.Errorf("services manager not started - call Start() first")
	}
	return nil
}

// Close shuts down the manager
func (m *Manager) Close() error {
	// First shutdown all services
	if err := m.Shutdown(); err != nil {
		tap.Logger(m.ctx).Error("error during shutdown", "error", err)
	}

	// Then cancel the context and close DB
	m.cancel()
	if m.db != nil {
		return m.db.Close()
	}
	return nil
}

// run is the main event loop
func (m *Manager) run() {
	// In-memory state
	states := make(map[string]*ServiceState)
	processes := make(map[string]*ProcessHandle)

	// Don't load services at startup - wait for commands that need the database

	for {
		select {
		case <-m.ctx.Done():
			return

		case cmd := <-m.commands:
			switch cmd.op {
			case opCreate:
				err := m.handleCreate(cmd.svc, states, processes)
				cmd.result <- err

			case opDelete:
				err := m.handleDelete(cmd.name, states, processes)
				cmd.result <- err

			case opStart:
				err := m.handleStart(cmd.name, states, processes)
				cmd.result <- err

			case opStop:
				err := m.handleStop(cmd.name, states, processes)
				cmd.result <- err

			case opShutdown:
				err := m.handleShutdown(states, processes)
				cmd.result <- err

			case opProcessExit:
				// Handle process exit notification
				if state, exists := states[cmd.name]; exists {
					state.PID = 0
					if cmd.exitCode == 0 || cmd.exitCode == -1 {
						state.Status = StatusStopped
						state.Error = ""
					} else {
						state.Status = StatusFailed
						state.Error = fmt.Sprintf("exited with code %d", cmd.exitCode)
					}
				}
				delete(processes, cmd.name)

				// Log the exit
				if cmd.exitCode == 0 {
					tap.Logger(m.ctx).Info("service stopped", "name", cmd.name, "exit_code", cmd.exitCode)
				} else if cmd.exitCode == -1 {
					tap.Logger(m.ctx).Info("service stopped", "name", cmd.name, "exit_code", "unknown")
				} else {
					tap.Logger(m.ctx).Error("service exited with error", "name", cmd.name, "exit_code", cmd.exitCode)
				}

				// No result to send for process exit
				if cmd.result != nil {
					cmd.result <- nil
				}

			case opSignal:
				// Send signal to a running service
				err := m.handleSignal(cmd.name, cmd.signal, states, processes)
				cmd.result <- err

			case opStartAll:
				// Start all services in dependency order
				err := m.handleStartAll(states, processes)
				cmd.result <- err

			case opGetProcessHandle:
				// Get process handle for a service
				handle, exists := processes[cmd.name]
				if !exists {
					cmd.result <- fmt.Errorf("service not running: %s", cmd.name)
				} else {
					cmd.result <- handle
				}
			}

		case req := <-m.stateRequests:
			state, exists := states[req.name]
			if !exists {
				req.result <- nil
			} else {
				// Return a copy to avoid race conditions
				stateCopy := *state
				req.result <- &stateCopy
			}
		}
	}
}

// Public API methods that send commands through channels

// CreateService creates a new service
func (m *Manager) CreateService(svc *Service) error {
	result := make(chan interface{})
	m.commands <- command{
		op:     opCreate,
		svc:    svc,
		result: result,
	}
	resp := <-result
	if resp == nil {
		return nil
	}
	return resp.(error)
}

// DeleteService deletes a service
func (m *Manager) DeleteService(name string) error {
	result := make(chan interface{})
	m.commands <- command{
		op:     opDelete,
		name:   name,
		result: result,
	}
	resp := <-result
	if resp == nil {
		return nil
	}
	return resp.(error)
}

// StopService stops a running service
func (m *Manager) StopService(name string) error {
	result := make(chan interface{})
	m.commands <- command{
		op:     opStop,
		name:   name,
		result: result,
	}
	resp := <-result
	if resp == nil {
		return nil
	}
	return resp.(error)
}

// GetServiceState returns the current state of a service
func (m *Manager) GetServiceState(name string) (*ServiceState, error) {
	result := make(chan *ServiceState)
	m.stateRequests <- stateRequest{
		name:   name,
		result: result,
	}
	state := <-result
	if state == nil {
		return nil, fmt.Errorf("service not found: %s", name)
	}
	return state, nil
}

// ListServices returns all registered services
func (m *Manager) ListServices() ([]*Service, error) {
	if err := m.ensureDB(); err != nil {
		return nil, err
	}
	return m.db.ListServices()
}

// GetService returns a service definition
func (m *Manager) GetService(name string) (*Service, error) {
	if err := m.ensureDB(); err != nil {
		return nil, err
	}
	return m.db.GetService(name)
}

// Shutdown stops all running services in reverse dependency order
func (m *Manager) Shutdown() error {
	result := make(chan interface{})
	m.commands <- command{
		op:     opShutdown,
		result: result,
	}
	resp := <-result
	if resp == nil {
		return nil
	}
	return resp.(error)
}

// StopForUnmount stops services and closes the database so underlying file
// handles under the mount point are released. It does NOT cancel the manager
// context, allowing a subsequent Start() to reopen the database.
func (m *Manager) StopForUnmount() error {
	// Stop services first
	if err := m.Shutdown(); err != nil {
		return err
	}
	// Close DB to release handles, but keep context for future restarts
	if m.db != nil {
		if err := m.db.Close(); err != nil {
			return err
		}
		m.db = nil
	}
	return nil
}

// StartService starts a single service by name
func (m *Manager) StartService(name string) error {
	result := make(chan interface{})
	m.commands <- command{
		op:     opStart,
		name:   name,
		result: result,
	}
	resp := <-result
	if resp == nil {
		return nil
	}
	return resp.(error)
}

// StartAndMonitor starts a service and monitors it for the given duration
// It returns information about whether the service started successfully and
// whether it completed (exited) within the monitoring duration
func (m *Manager) StartAndMonitor(name string, duration time.Duration) (*StartResult, error) {
	// Start the service
	err := m.StartService(name)
	if err != nil {
		return &StartResult{
			Started: false,
			Error:   err,
		}, nil
	}

	// Create a context with the monitoring duration
	ctx, cancel := context.WithTimeout(m.ctx, duration)
	defer cancel()

	// Monitor the service for the specified duration
	ticker := time.NewTicker(50 * time.Millisecond)
	defer ticker.Stop()

	for {
		select {
		case <-ctx.Done():
			// Monitoring duration reached, service still running
			return &StartResult{
				Started:   true,
				Completed: false,
			}, nil
		case <-ticker.C:
			state, err := m.GetServiceState(name)
			if err != nil {
				// Service might have been deleted
				return &StartResult{
					Started:   true,
					Completed: true,
					ExitCode:  -1,
					Error:     err,
				}, nil
			}
			if state.Status == StatusStopped || state.Status == StatusFailed {
				// Service has stopped
				exitCode := 0
				if state.Status == StatusFailed && state.Error != "" {
					// Try to parse exit code from error message "exited with code X"
					var code int
					if _, err := fmt.Sscanf(state.Error, "exited with code %d", &code); err == nil {
						exitCode = code
					} else {
						exitCode = 1 // Default non-zero for failed status
					}
				}
				return &StartResult{
					Started:   true,
					Completed: true,
					ExitCode:  exitCode,
				}, nil
			}
		}
	}
}

// StartAll starts all services in dependency order
func (m *Manager) StartAll() error {
	result := make(chan interface{})
	m.commands <- command{
		op:     opStartAll,
		result: result,
	}
	resp := <-result
	if resp == nil {
		return nil
	}
	return resp.(error)
}

// WaitForStop waits for a service to reach stopped state
func (m *Manager) WaitForStop(name string, timeout time.Duration) error {
	ctx, cancel := context.WithTimeout(m.ctx, timeout)
	defer cancel()

	ticker := time.NewTicker(100 * time.Millisecond)
	defer ticker.Stop()

	for {
		select {
		case <-ctx.Done():
			return fmt.Errorf("timeout waiting for service %s to stop", name)
		case <-ticker.C:
			state, err := m.GetServiceState(name)
			if err != nil {
				// Service might have been deleted
				return nil
			}
			if state.Status == StatusStopped || state.Status == StatusFailed {
				return nil
			}
		}
	}
}

// SignalService sends a signal to a running service
func (m *Manager) SignalService(name string, signal string) error {
	result := make(chan interface{})
	m.commands <- command{
		op:     opSignal,
		name:   name,
		signal: signal,
		result: result,
	}
	resp := <-result
	if resp == nil {
		return nil
	}
	return resp.(error)
}

// GetProcessHandle returns the ProcessHandle for a running service
// This allows attaching/removing writers to stdout/stderr at runtime
func (m *Manager) GetProcessHandle(name string) (*ProcessHandle, error) {
	result := make(chan interface{})
	m.commands <- command{
		op:     opGetProcessHandle,
		name:   name,
		result: result,
	}
	resp := <-result
	if err, ok := resp.(error); ok {
		return nil, err
	}
	return resp.(*ProcessHandle), nil
}

// WaitForService waits for a service to exit and returns the exit code.
// Returns an error if the timeout is reached before the service exits.
func (m *Manager) WaitForService(name string, timeout time.Duration) (int, error) {
	handle, err := m.GetProcessHandle(name)
	if err != nil {
		return 0, err
	}
	return handle.Wait(timeout)
}
