package services

import (
	"context"
	"fmt"
	"time"

	"github.com/superfly/sprite-env/pkg/tap"
)

// BaseManager manages service lifecycle and dependencies in-memory only
// This is the core plumbing for service management without database persistence
type BaseManager struct {
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

	// Service definitions for managed services (in-memory only)
	serviceDefs map[string]*ServiceDefinition

	// Verifiers for external resources (check actual system state)
	setupVerifiers   []func(context.Context) error // verify resources exist
	cleanupVerifiers []func(context.Context) error // verify resources cleaned up
}

// NewBaseManager creates a new in-memory service manager
// This manager does NOT use a database and is suitable for system services
func NewBaseManager(opts ...BaseOption) (*BaseManager, error) {
	ctx, cancel := context.WithCancel(context.Background())

	// Tag logger with "services" component
	logger := tap.Logger(ctx).With("component", "services")
	ctx = tap.WithLogger(ctx, logger)

	m := &BaseManager{
		commands:      make(chan command),
		stateRequests: make(chan stateRequest),
		ctx:           ctx,
		cancel:        cancel,
		stopCh:        make(chan struct{}),
		stoppedCh:     make(chan struct{}),
		errCh:         make(chan error, 1),
		serviceDefs:   make(map[string]*ServiceDefinition),
	}

	// Apply options
	for _, opt := range opts {
		opt(m)
	}

	// Start the manager loop
	go m.run()

	return m, nil
}

// BaseOption configures the BaseManager
type BaseOption func(*BaseManager)

// WithLogDirBase sets the directory for service logs (for BaseManager)
func WithLogDirBase(logDir string) BaseOption {
	return func(m *BaseManager) {
		m.logDir = logDir
	}
}

// SetCmdPrefix sets the command prefix for service execution
func (m *BaseManager) SetCmdPrefix(prefix []string) {
	m.cmdPrefix = prefix
	tap.Logger(m.ctx).Info("Service manager command prefix has been set", "prefix", prefix)
}

// run is the main event loop
func (m *BaseManager) run() {
	// In-memory state
	states := make(map[string]*ServiceState)
	processes := make(map[string]*ProcessHandle)

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
			case opRegisterService:
				// Register a service definition
				err := m.handleRegisterService(cmd.svcDef, states)
				cmd.result <- err

			case opStartAll:
				// Start all services in dependency order
				err := m.handleStartAll(states, processes)
				cmd.result <- err

			case opShutdown:
				err := m.handleShutdown(states, processes)
				cmd.result <- err

			case opStopServiceTree:
				// Stop a service and all its dependents
				err := m.handleStopServiceTree(cmd.name, states, processes)
				cmd.result <- err

			case opStartServiceTree:
				// Start a service and all its dependencies
				err := m.handleStartServiceTree(cmd.name, states, processes)
				cmd.result <- err

			case opGetAllStates:
				// Get all service states
				allStates := make(map[string]*ServiceState)
				for name, state := range states {
					stateCopy := *state
					allStates[name] = &stateCopy
				}
				cmd.result <- allStates

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

// RegisterService registers a ServiceDefinition for management
func (m *BaseManager) RegisterService(svcDef *ServiceDefinition) error {
	if svcDef == nil {
		return fmt.Errorf("service definition cannot be nil")
	}
	if svcDef.Name == "" {
		return fmt.Errorf("service name cannot be empty")
	}
	if svcDef.ManagedService == nil && svcDef.ProcessService == nil && (svcDef.Hooks == nil || (svcDef.Hooks.Start == nil && svcDef.Hooks.Stop == nil)) {
		return fmt.Errorf("service definition must have Hooks, ManagedService or ProcessService")
	}

	result := make(chan interface{})
	m.commands <- command{
		op:     opRegisterService,
		svcDef: svcDef,
		result: result,
	}
	resp := <-result
	if resp == nil {
		return nil
	}
	return resp.(error)
}

// StartAll starts all registered services in dependency order
func (m *BaseManager) StartAll() error {
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

// Shutdown stops all running services in reverse dependency order
func (m *BaseManager) Shutdown() error {
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

// StopServiceTree stops a service and all services that depend on it
func (m *BaseManager) StopServiceTree(rootService string) error {
	result := make(chan interface{})
	m.commands <- command{
		op:     opStopServiceTree,
		name:   rootService,
		result: result,
	}
	resp := <-result
	if resp == nil {
		return nil
	}
	return resp.(error)
}

// GetServiceState returns the current state of a service
func (m *BaseManager) GetServiceState(name string) (*ServiceState, error) {
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

// getAllStates returns all service states (internal helper)
func (m *BaseManager) getAllStates() map[string]*ServiceState {
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

// Stop shuts down the manager
func (m *BaseManager) Stop(ctx context.Context) error {
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

	// Shutdown services BEFORE cancelling context
	if err := m.Shutdown(); err != nil {
		tap.Logger(m.ctx).Error("error during shutdown", "error", err)
	}

	// Add cleanup verifiers for each process that was running
	for _, pid := range runningPIDs {
		capturedPID := pid
		m.cleanupVerifiers = append(m.cleanupVerifiers, func(ctx context.Context) error {
			if processExists(capturedPID) {
				return fmt.Errorf("service process still running: PID %d (check: ps -p %d)", capturedPID, capturedPID)
			}
			return nil
		})
	}

	// Cancel the context to stop the run loop
	m.cancel()

	// Wait for run loop to complete
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

// Wait blocks until Stop() completes or a panic occurs
func (m *BaseManager) Wait() error {
	select {
	case <-m.stoppedCh:
		return nil
	case err := <-m.errCh:
		return err
	}
}

// SetupVerifiers returns functions that verify resources are set up correctly
func (m *BaseManager) SetupVerifiers() []func(context.Context) error {
	return m.setupVerifiers
}

// CleanupVerifiers returns functions that verify resources are cleaned up
func (m *BaseManager) CleanupVerifiers() []func(context.Context) error {
	return m.cleanupVerifiers
}

// StartServiceTree starts a service and all its dependencies
// This is useful for partial restarts (e.g., restarting container after a restore)
func (m *BaseManager) StartServiceTree(serviceName string) error {
	result := make(chan interface{})
	m.commands <- command{
		op:     opStartServiceTree,
		name:   serviceName,
		result: result,
	}
	resp := <-result
	if resp == nil {
		return nil
	}
	return resp.(error)
}

// handleStartServiceTree starts a service and all its dependencies
func (m *BaseManager) handleStartServiceTree(serviceName string, states map[string]*ServiceState, processes map[string]*ProcessHandle) error {
	// Collect all dependencies
	deps := m.collectDependencies(serviceName)
	toStart := append(deps, serviceName)

	tap.Logger(m.ctx).Info("starting service tree", "root", serviceName, "total", len(toStart), "order", toStart)

	// Start each service in dependency order
	for _, name := range toStart {
		svcDef, ok := m.serviceDefs[name]
		if !ok {
			return fmt.Errorf("service not found: %s", name)
		}

		// Check current state
		state, exists := states[name]
		if exists && state.Status == StatusRunning {
			tap.Logger(m.ctx).Info("service already running, skipping", "name", name)
			continue
		}

		// Ensure state exists
		if !exists {
			states[name] = &ServiceState{
				Name:   name,
				Status: StatusStopped,
			}
			state = states[name]
		}

		tap.Logger(m.ctx).Info("starting service in tree", "name", name)

		// Start the service
		progress := newProgressReporter(name, tap.Logger(m.ctx))

		var startErr error
		if svcDef.Hooks != nil && svcDef.Hooks.Start != nil {
			startErr = svcDef.Hooks.Start(m.ctx, progress)
		} else if svcDef.ManagedService != nil {
			startErr = svcDef.ManagedService.Start(m.ctx, progress)
		} else {
			startErr = fmt.Errorf("service %s has no Start hook or ManagedService", name)
		}
		if startErr != nil {
			state.Status = StatusFailed
			state.Error = startErr.Error()
			return fmt.Errorf("failed to start %s: %w", name, startErr)
		}

		// Update state to running
		state.Status = StatusRunning
		state.StartedAt = time.Now()
		tap.Logger(m.ctx).Info("service started in tree", "name", name, "status", state.Status)
	}

	tap.Logger(m.ctx).Info("service tree started", "root", serviceName)
	return nil
}

// collectDependencies collects all transitive dependencies of a service
func (m *BaseManager) collectDependencies(serviceName string) []string {
	visited := make(map[string]bool)
	var result []string

	var visit func(string)
	visit = func(name string) {
		if visited[name] {
			return
		}
		visited[name] = true

		svcDef, ok := m.serviceDefs[name]
		if !ok {
			return
		}

		// Visit dependencies first
		for _, dep := range svcDef.Dependencies {
			visit(dep)
			if !containsString(result, dep) {
				result = append(result, dep)
			}
		}
	}

	visit(serviceName)
	return result
}

// handleRegisterService handles registration of a ServiceDefinition
func (m *BaseManager) handleRegisterService(svcDef *ServiceDefinition, states map[string]*ServiceState) error {
	// Validate the service definition
	if svcDef.Name == "" {
		return fmt.Errorf("service name cannot be empty")
	}

	// Check if service already registered
	if _, exists := m.serviceDefs[svcDef.Name]; exists {
		return fmt.Errorf("service %s already registered", svcDef.Name)
	}

	// Store the service definition
	m.serviceDefs[svcDef.Name] = svcDef

	// Initialize state for the service
	states[svcDef.Name] = &ServiceState{
		Name:   svcDef.Name,
		Status: StatusStopped,
	}

	tap.Logger(m.ctx).Info("service registered", "name", svcDef.Name)
	return nil
}

// handleStartAll starts all services in dependency order
func (m *BaseManager) handleStartAll(states map[string]*ServiceState, processes map[string]*ProcessHandle) error {
	// Use only serviceDefs (no database)
	if len(m.serviceDefs) == 0 {
		tap.Logger(m.ctx).Info("no services to start")
		return nil
	}

	// Build dependency map
	deps := make(map[string][]string)
	for name, svcDef := range m.serviceDefs {
		deps[name] = svcDef.Dependencies
	}

	// Calculate start order
	order, err := calculateStartOrder(deps)
	if err != nil {
		return fmt.Errorf("failed to calculate start order: %w", err)
	}

	// Group by dependency level for parallel starting
	levels := groupByDependencyLevelFromDeps(order, deps)

	tap.Logger(m.ctx).Info("starting all services", "total", len(m.serviceDefs))

	// Ensure all services have state entries
	for name := range m.serviceDefs {
		if _, exists := states[name]; !exists {
			states[name] = &ServiceState{
				Name:   name,
				Status: StatusStopped,
			}
		}
	}

	// Start services level by level (parallel within each level)
	for level, servicesAtLevel := range levels {
		if len(servicesAtLevel) == 0 {
			continue
		}

		tap.Logger(m.ctx).Info("starting services at dependency level", "level", level, "count", len(servicesAtLevel))

		// Start all services at this level in parallel
		errChan := make(chan error, len(servicesAtLevel))
		for _, name := range servicesAtLevel {
			go func(svcName string) {
				svcDef := m.serviceDefs[svcName]

				// Start based on type
				if svcDef.Hooks != nil && svcDef.Hooks.Start != nil {
					tap.Logger(m.ctx).Info("starting managed service (hooks)", "name", svcName)
					progress := newProgressReporter(svcName, tap.Logger(m.ctx))
					err := svcDef.Hooks.Start(m.ctx, progress)
					if err != nil {
						tap.Logger(m.ctx).Error("failed to start managed service (hooks)", "name", svcName, "error", err)
						errChan <- fmt.Errorf("service %s: %w", svcName, err)
					} else {
						if state, exists := states[svcName]; exists {
							state.Status = StatusRunning
						}
						tap.Logger(m.ctx).Info("managed service started successfully", "name", svcName)
						errChan <- nil
					}
				} else if svcDef.ManagedService != nil {
					tap.Logger(m.ctx).Info("starting managed service", "name", svcName)

					// Create progress reporter
					progress := newProgressReporter(svcName, tap.Logger(m.ctx))

					// Call Start directly
					err := svcDef.ManagedService.Start(m.ctx, progress)
					if err != nil {
						tap.Logger(m.ctx).Error("failed to start managed service", "name", svcName, "error", err)
						errChan <- fmt.Errorf("service %s: %w", svcName, err)
					} else {
						// Update state to running
						if state, exists := states[svcName]; exists {
							state.Status = StatusRunning
						}
						tap.Logger(m.ctx).Info("managed service started successfully", "name", svcName)
						errChan <- nil
					}
				} else {
					errChan <- fmt.Errorf("BaseManager only supports ManagedService, not ProcessService: %s", svcName)
				}
			}(name)
		}

		// Wait for all services at this level to complete
		var levelErrors []error
		for i := 0; i < len(servicesAtLevel); i++ {
			if err := <-errChan; err != nil {
				levelErrors = append(levelErrors, err)
			}
		}

		// If any service failed at this level, stop
		if len(levelErrors) > 0 {
			return fmt.Errorf("level %d failed with %d errors: %v", level, len(levelErrors), levelErrors)
		}
	}

	tap.Logger(m.ctx).Info("finished starting all services", "total", len(m.serviceDefs))
	return nil
}

// handleShutdown stops all services in reverse dependency order
func (m *BaseManager) handleShutdown(states map[string]*ServiceState, processes map[string]*ProcessHandle) error {
	return handleShutdownInternal(m.ctx, m.serviceDefs, nil, states, processes)
}

// handleStopServiceTree stops a service and all services that depend on it
func (m *BaseManager) handleStopServiceTree(rootService string, states map[string]*ServiceState, processes map[string]*ProcessHandle) error {
	return handleStopServiceTreeInternal(m.ctx, m.serviceDefs, nil, rootService, states, processes)
}

// groupByDependencyLevelFromDeps groups services by their dependency level using just the deps map
func groupByDependencyLevelFromDeps(order []string, deps map[string][]string) [][]string {
	// Calculate levels
	levels := make(map[string]int)
	var calcLevel func(name string) int
	calcLevel = func(name string) int {
		if level, exists := levels[name]; exists {
			return level
		}

		maxDepLevel := -1
		for _, dep := range deps[name] {
			depLevel := calcLevel(dep)
			if depLevel > maxDepLevel {
				maxDepLevel = depLevel
			}
		}

		levels[name] = maxDepLevel + 1
		return maxDepLevel + 1
	}

	// Calculate level for all services
	maxLevel := -1
	for _, name := range order {
		level := calcLevel(name)
		if level > maxLevel {
			maxLevel = level
		}
	}

	// Group by level
	result := make([][]string, maxLevel+1)
	for name, level := range levels {
		result[level] = append(result[level], name)
	}

	return result
}
