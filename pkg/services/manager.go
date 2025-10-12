package services

import (
	"context"
	"fmt"
	"os"
	"syscall"
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

	// Lifecycle channels
	stopCh    chan struct{} // closed to request shutdown
	stoppedCh chan struct{} // closed when shutdown complete
	errCh     chan error    // buffered, reports panics

	// State (plain bool, no mutex needed for simple flag)
	started bool

	// Verifiers for external resources (check actual system state)
	setupVerifiers   []func(context.Context) error // verify resources exist
	cleanupVerifiers []func(context.Context) error // verify resources cleaned up
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
	opGetAllStates
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

	// Tag logger with "services" component
	logger := tap.Logger(ctx).With("component", "services")
	ctx = tap.WithLogger(ctx, logger)

	m := &Manager{
		dataDir:       dataDir,
		commands:      make(chan command),
		stateRequests: make(chan stateRequest),
		ctx:           ctx,
		cancel:        cancel,
		stopCh:        make(chan struct{}),
		stoppedCh:     make(chan struct{}),
		errCh:         make(chan error, 1),
	}

	// Apply options
	for _, opt := range opts {
		opt(m)
	}

	// Start the manager loop (this is OK - just starts the event loop)
	go m.run()

	return m, nil
}

// SetCmdPrefix sets the command prefix for service execution
func (m *Manager) SetCmdPrefix(prefix []string) {
	m.cmdPrefix = prefix
	tap.Logger(m.ctx).Info("Service manager command prefix has been set", "prefix", prefix)
}

// Start initializes the database and prepares the manager
// Returns error if already started (NOT idempotent)
func (m *Manager) Start() error {
	if m.started {
		return fmt.Errorf("services manager already started")
	}
	m.started = true

	// Recreate channels for restartability (in case this is a restart after Stop)
	select {
	case <-m.stoppedCh:
		// Channels were closed, recreate them
		m.stopCh = make(chan struct{})
		m.stoppedCh = make(chan struct{})
		m.errCh = make(chan error, 1)
		// Recreate context
		m.ctx, m.cancel = context.WithCancel(context.Background())
		// Restart the run loop
		go m.run()
	default:
		// Channels are still open, first start
	}

	// Clear verifiers from any previous run
	m.setupVerifiers = nil
	m.cleanupVerifiers = nil

	// CRITICAL: Create log directory FIRST, before DB
	// Services need log directory to exist before they start
	if m.logDir != "" {
		logDir := fmt.Sprintf("%s/services", m.logDir)
		if err := os.MkdirAll(logDir, 0755); err != nil {
			return fmt.Errorf("failed to create log directory: %w", err)
		}
		// Add setup verifier for log directory
		m.setupVerifiers = append(m.setupVerifiers, func(ctx context.Context) error {
			if _, err := os.Stat(logDir); os.IsNotExist(err) {
				return fmt.Errorf("log directory does not exist: %s", logDir)
			}
			return nil
		})
	}

	// THEN: Open database
	fmt.Printf("Starting services manager, initializing database in %s\n", m.dataDir)
	db, err := NewDB(m.dataDir)
	if err != nil {
		return fmt.Errorf("failed to create database: %w", err)
	}
	m.db = db

	// Add setup verifier for database file
	dbPath := fmt.Sprintf("%s/services.db", m.dataDir)
	m.setupVerifiers = append(m.setupVerifiers, func(ctx context.Context) error {
		if _, err := os.Stat(dbPath); os.IsNotExist(err) {
			return fmt.Errorf("database file does not exist: %s", dbPath)
		}
		return nil
	})

	tap.Logger(m.ctx).Info("Services manager started", "dataDir", m.dataDir)

	// Automatically start all services
	tap.Logger(m.ctx).Info("Starting all services")
	if err := m.StartAll(); err != nil {
		tap.Logger(m.ctx).Error("Failed to start services", "error", err)
		// Non-fatal error - services manager is still operational
	} else {
		tap.Logger(m.ctx).Info("All services started successfully")
	}

	return nil
}

// ensureDB checks if the database is initialized
func (m *Manager) ensureDB() error {
	if m.db == nil {
		return fmt.Errorf("services manager not started - call Start() first")
	}
	return nil
}

// Wait blocks until Stop() completes or a panic occurs
// Can be called multiple times safely
func (m *Manager) Wait() error {
	select {
	case <-m.stoppedCh:
		return nil
	case err := <-m.errCh:
		return err
	}
}

// getAllStates returns all service states (internal helper for Stop)
func (m *Manager) getAllStates() map[string]*ServiceState {
	result := make(chan interface{})
	select {
	case m.commands <- command{
		op:     opGetAllStates,
		result: result,
	}:
		resp := <-result
		if states, ok := resp.(map[string]*ServiceState); ok {
			return states
		}
		return nil
	case <-m.ctx.Done():
		return nil
	}
}

// Stop initiates shutdown then waits for completion
// Can be called multiple times safely (idempotent)
func (m *Manager) Stop(ctx context.Context) error {
	// If manager was never started, treat Stop as no-op (idempotent)
	if !m.started {
		return nil
	}
	// Check if already stopped
	select {
	case <-m.stoppedCh:
		// Already stopped
		return nil
	default:
	}

	// Signal shutdown request
	select {
	case <-m.stopCh:
		// Already signaled
	default:
		close(m.stopCh)
	}

	// Capture running service PIDs BEFORE shutdown for verification
	var runningPIDs []int
	states := m.getAllStates()
	for _, state := range states {
		if state.Status == StatusRunning && state.PID > 0 {
			runningPIDs = append(runningPIDs, state.PID)
		}
	}

	// Shutdown services BEFORE cancelling context (so run loop can process the command)
	if err := m.Shutdown(); err != nil {
		tap.Logger(m.ctx).Error("error during shutdown", "error", err)
	}

	// Add cleanup verifiers for each process that was running
	for _, pid := range runningPIDs {
		capturedPID := pid // Capture for closure
		m.cleanupVerifiers = append(m.cleanupVerifiers, func(ctx context.Context) error {
			if processExists(capturedPID) {
				return fmt.Errorf("service process still running: PID %d (check: ps -p %d)", capturedPID, capturedPID)
			}
			return nil
		})
	}

	// Close DB to release handles
	if m.db != nil {
		if err := m.db.Close(); err != nil {
			tap.Logger(m.ctx).Error("error closing database", "error", err)
		}
		m.db = nil
	}

	// Cancel the context to stop the run loop
	m.cancel()

	// Wait for run loop to complete (with timeout from ctx)
	select {
	case <-m.stoppedCh:
		// Run loop completed
	case <-ctx.Done():
		return fmt.Errorf("timeout waiting for services manager to stop")
	}

	// Mark as not started so it can be restarted
	m.started = false

	return nil
}

// Close shuts down the manager
// Deprecated: Use Stop() instead
func (m *Manager) Close() error {
	// Create a context with reasonable timeout
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()
	return m.Stop(ctx)
}

// run is the main event loop
func (m *Manager) run() {
	// In-memory state
	states := make(map[string]*ServiceState)
	processes := make(map[string]*ProcessHandle)

	// Don't load services at startup - wait for commands that need the database

	defer func() {
		// Signal that run loop has exited
		select {
		case <-m.stoppedCh:
			// Already closed
		default:
			close(m.stoppedCh)
		}
	}()

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

			case opGetAllStates:
				// Get all service states
				allStates := make(map[string]*ServiceState)
				for name, state := range states {
					stateCopy := *state
					allStates[name] = &stateCopy
				}
				cmd.result <- allStates
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

// SetupVerifiers returns functions that verify resources are set up correctly
// Each function checks actual system state (files, processes, etc.)
func (m *Manager) SetupVerifiers() []func(context.Context) error {
	return m.setupVerifiers
}

// CleanupVerifiers returns functions that verify resources are cleaned up
// Each function checks actual system state (files, processes, etc.)
func (m *Manager) CleanupVerifiers() []func(context.Context) error {
	return m.cleanupVerifiers
}

// processExists checks if a process with the given PID is still running
func processExists(pid int) bool {
	process, err := os.FindProcess(pid)
	if err != nil {
		return false
	}
	// On Unix, FindProcess always succeeds, so we need to send signal 0 to check
	// Signal 0 doesn't actually send a signal, just checks if process exists
	err = process.Signal(syscall.Signal(0))
	return err == nil
}
