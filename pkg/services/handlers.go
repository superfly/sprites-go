package services

import (
	"fmt"
	"os"
	"strings"
	"syscall"

	"github.com/superfly/sprite-env/pkg/tap"
)

// handleCreate handles service creation
func (m *Manager) handleCreate(svc *Service, states map[string]*ServiceState, processes map[string]*ProcessHandle) error {
	// Ensure database is initialized
	if err := m.ensureDB(); err != nil {
		return fmt.Errorf("failed to initialize database: %w", err)
	}

	// Validate dependencies
	if err := m.validateDependencies(svc); err != nil {
		return fmt.Errorf("dependency validation failed: %w", err)
	}

	// Store in database
	if err := m.db.CreateService(svc); err != nil {
		return fmt.Errorf("failed to store service: %w", err)
	}

	// Add to state map as stopped
	states[svc.Name] = &ServiceState{
		Name:   svc.Name,
		Status: StatusStopped,
	}

	tap.Logger(m.ctx).Info("service created", "name", svc.Name)
	return nil
}

// handleDelete handles service deletion
func (m *Manager) handleDelete(name string, states map[string]*ServiceState, processes map[string]*ProcessHandle) error {
	// Ensure database is initialized
	if err := m.ensureDB(); err != nil {
		return fmt.Errorf("failed to initialize database: %w", err)
	}

	// Check if service exists in database
	svc, err := m.db.GetService(name)
	if err != nil {
		if strings.Contains(err.Error(), "not found") {
			return fmt.Errorf("service not found: %s", name)
		}
		return fmt.Errorf("failed to get service: %w", err)
	}

	// Check if service is in states map (i.e., it's been managed in this session)
	state, exists := states[name]
	if exists {
		// Stop the service if it's running
		if state.Status == StatusRunning || state.Status == StatusStarting {
			if err := m.stopService(name, states, processes); err != nil {
				return fmt.Errorf("failed to stop service before deletion: %w", err)
			}
		}
	} else {
		// Service exists in DB but not in current session
		// Add a placeholder state so we can track it
		states[name] = &ServiceState{
			Name:   svc.Name,
			Status: StatusStopped,
		}
	}

	// Check if other services depend on this one
	services, err := m.db.ListServices()
	if err != nil {
		return fmt.Errorf("failed to check dependencies: %w", err)
	}

	for _, svc := range services {
		for _, need := range svc.Needs {
			if need == name {
				return fmt.Errorf("service %s depends on %s", svc.Name, name)
			}
		}
	}

	// Delete from database
	if err := m.db.DeleteService(name); err != nil {
		return fmt.Errorf("failed to delete service: %w", err)
	}

	// Remove from state map and processes
	delete(states, name)
	delete(processes, name)

	tap.Logger(m.ctx).Info("service deleted", "name", name)
	return nil
}

// handleStart handles service start requests
func (m *Manager) handleStart(name string, states map[string]*ServiceState, processes map[string]*ProcessHandle) error {
	// Get the service
	svc, err := m.db.GetService(name)
	if err != nil {
		return fmt.Errorf("failed to get service: %w", err)
	}

	// Ensure state entry exists (in case service was in DB but not in memory)
	if _, exists := states[svc.Name]; !exists {
		states[svc.Name] = &ServiceState{
			Name:   svc.Name,
			Status: StatusStopped,
		}
	}

	return m.startService(svc, states, processes)
}

// handleStop handles service stop requests
func (m *Manager) handleStop(name string, states map[string]*ServiceState, processes map[string]*ProcessHandle) error {
	return m.stopService(name, states, processes)
}

// handleSignal sends a signal to a running service
func (m *Manager) handleSignal(name string, signal string, states map[string]*ServiceState, processes map[string]*ProcessHandle) error {
	state, exists := states[name]
	if !exists {
		return fmt.Errorf("service not found: %s", name)
	}

	if state.Status != StatusRunning {
		return fmt.Errorf("service %s is not running", name)
	}

	handle, exists := processes[name]
	if !exists || handle == nil {
		return fmt.Errorf("process handle not found for service %s", name)
	}

	// Parse signal
	sig, err := parseSignal(signal)
	if err != nil {
		return fmt.Errorf("invalid signal: %w", err)
	}

	// Find the process
	proc, err := os.FindProcess(handle.PID)
	if err != nil {
		return fmt.Errorf("failed to find process: %w", err)
	}

	// Send the signal
	if err := proc.Signal(sig); err != nil {
		return fmt.Errorf("failed to send signal: %w", err)
	}

	tap.Logger(m.ctx).Info("sent signal to service", "name", name, "signal", signal, "pid", handle.PID)
	return nil
}

// parseSignal converts a signal string to os.Signal
func parseSignal(signal string) (os.Signal, error) {
	switch strings.ToUpper(signal) {
	case "TERM", "SIGTERM":
		return syscall.SIGTERM, nil
	case "KILL", "SIGKILL":
		return syscall.SIGKILL, nil
	case "INT", "SIGINT":
		return syscall.SIGINT, nil
	case "HUP", "SIGHUP":
		return syscall.SIGHUP, nil
	case "USR1", "SIGUSR1":
		return syscall.SIGUSR1, nil
	case "USR2", "SIGUSR2":
		return syscall.SIGUSR2, nil
	default:
		return nil, fmt.Errorf("unknown signal: %s", signal)
	}
}

// handleStartAll starts all services in dependency order
func (m *Manager) handleStartAll(states map[string]*ServiceState, processes map[string]*ProcessHandle) error {
	// Ensure database is initialized
	if err := m.ensureDB(); err != nil {
		return fmt.Errorf("failed to initialize database: %w", err)
	}

	// Get all services from the database
	services, err := m.db.ListServices()
	if err != nil {
		return fmt.Errorf("failed to list services: %w", err)
	}

	if len(services) == 0 {
		tap.Logger(m.ctx).Info("no services to start")
		return nil
	}

	// Build dependency graph and calculate start order
	deps := make(map[string][]string)
	for _, svc := range services {
		deps[svc.Name] = svc.Needs
	}

	// Calculate start order (dependencies before dependents)
	order, err := calculateStartOrder(deps)
	if err != nil {
		return fmt.Errorf("failed to calculate start order: %w", err)
	}

	// Group by dependency level for parallel starting
	levels := m.groupByDependencyLevel(order, services)

	tap.Logger(m.ctx).Info("starting all services", "total", len(services))

	// First, ensure all services have state entries
	for _, svc := range services {
		if _, exists := states[svc.Name]; !exists {
			// Add state entry for service loaded from database
			states[svc.Name] = &ServiceState{
				Name:   svc.Name,
				Status: StatusStopped,
			}
		}
	}

	// Start services level by level
	for level := 0; level < len(levels); level++ {
		servicesAtLevel := levels[level]
		tap.Logger(m.ctx).Info("starting services at dependency level", "level", level, "count", len(servicesAtLevel))

		// Start all services at this level
		for _, name := range servicesAtLevel {
			// Find the service definition
			var svc *Service
			for _, s := range services {
				if s.Name == name {
					svc = s
					break
				}
			}
			if svc == nil {
				tap.Logger(m.ctx).Error("service definition not found", "name", name)
				continue
			}

			// Log before starting
			tap.Logger(m.ctx).Info("starting service", "name", name, "cmd", svc.Cmd)

			// Start the service
			if err := m.startService(svc, states, processes); err != nil {
				tap.Logger(m.ctx).Error("failed to start service", "name", name, "error", err)
				// Continue with other services instead of failing entirely
			} else {
				tap.Logger(m.ctx).Info("service started successfully", "name", name)
			}
		}
	}

	tap.Logger(m.ctx).Info("finished starting all services", "total", len(services))
	return nil
}
