package services

import (
	"fmt"
	"os"
	"strings"
	"syscall"
	"time"

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
	// Collect all services from both serviceDefs and database
	allServices := make(map[string]interface{}) // name -> *ServiceDefinition or *Service
	deps := make(map[string][]string)

	// Add registered service definitions (managed services)
	for name, svcDef := range m.serviceDefs {
		allServices[name] = svcDef
		deps[name] = svcDef.Dependencies
	}

	// Add database services (process-based services) if database is available
	if m.db != nil {
		services, err := m.db.ListServices()
		if err != nil {
			tap.Logger(m.ctx).Warn("failed to list database services", "error", err)
		} else {
			for _, svc := range services {
				// Only add if not already registered as a ServiceDefinition
				if _, exists := allServices[svc.Name]; !exists {
					allServices[svc.Name] = svc
					deps[svc.Name] = svc.Needs
				}
			}
		}
	}

	if len(allServices) == 0 {
		tap.Logger(m.ctx).Info("no services to start")
		return nil
	}

	// Calculate start order (dependencies before dependents)
	order, err := calculateStartOrder(deps)
	if err != nil {
		return fmt.Errorf("failed to calculate start order: %w", err)
	}

	// Group by dependency level for parallel starting
	levels := m.groupByDependencyLevelFromDeps(order, deps)

	tap.Logger(m.ctx).Info("starting all services", "total", len(allServices))

	// First, ensure all services have state entries
	for name := range allServices {
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
				// Get the service or service definition
				svcOrDef := allServices[svcName]

				// Start based on type
                if svcDef, ok := svcOrDef.(*ServiceDefinition); ok {
					// Managed service - call Start directly (we're in event loop context)
                    tap.Logger(m.ctx).Info("starting managed service", "name", svcName)

                    // Create progress reporter
                    progress := newProgressReporter(svcName, tap.Logger(m.ctx))

                    // Call Start directly to avoid deadlock
                    var err error
                    if svcDef.Hooks != nil && svcDef.Hooks.Start != nil {
                        err = svcDef.Hooks.Start(m.ctx, progress)
                    } else if svcDef.ManagedService != nil {
                        err = svcDef.ManagedService.Start(m.ctx, progress)
                    } else {
                        err = fmt.Errorf("service %s has no Start hook or ManagedService", svcName)
                    }
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
				} else if svc, ok := svcOrDef.(*Service); ok {
					// Process-based service
					tap.Logger(m.ctx).Info("starting process service", "name", svcName, "cmd", svc.Cmd)
					err := m.startService(svc, states, processes)
					if err != nil {
						tap.Logger(m.ctx).Error("failed to start process service", "name", svcName, "error", err)
						errChan <- fmt.Errorf("service %s: %w", svcName, err)
					} else {
						tap.Logger(m.ctx).Info("process service started successfully", "name", svcName)
						errChan <- nil
					}
				} else {
					errChan <- fmt.Errorf("unknown service type for %s", svcName)
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

	tap.Logger(m.ctx).Info("finished starting all services", "total", len(allServices))
	return nil
}

// groupByDependencyLevelFromDeps groups services by their dependency level using just the deps map
func (m *Manager) groupByDependencyLevelFromDeps(order []string, deps map[string][]string) [][]string {
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

// handleRegisterService handles registration of a ServiceDefinition
func (m *Manager) handleRegisterService(svcDef *ServiceDefinition, states map[string]*ServiceState) error {
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

// handleStopServiceTree stops a service and all services that depend on it
func (m *Manager) handleStopServiceTree(rootService string, states map[string]*ServiceState, processes map[string]*ProcessHandle) error {
	// Build dependency tree to find all services that depend on rootService
	dependents := make(map[string][]string)

	// Check both service definitions and database services
	for name, svcDef := range m.serviceDefs {
		for _, dep := range svcDef.Dependencies {
			dependents[dep] = append(dependents[dep], name)
		}
	}

	// Also check database services if DB is initialized
	if m.db != nil {
		services, err := m.db.ListServices()
		if err == nil {
			for _, svc := range services {
				for _, dep := range svc.Needs {
					if !containsString(dependents[dep], svc.Name) {
						dependents[dep] = append(dependents[dep], svc.Name)
					}
				}
			}
		}
	}

	// Find all services that transitively depend on rootService
	toStop := findTransitiveDependents(rootService, dependents)

	// findTransitiveDependents already returns in DFS order (dependents first)
	// Just append the root service at the end
	stopOrder := append(toStop, rootService)

	tap.Logger(m.ctx).Info("stopping service tree", "root", rootService, "total", len(stopOrder))

	// Stop each service in order (without dependency checks since we already have correct order)
	var firstErr error
	for _, name := range stopOrder {
		state, exists := states[name]
		if !exists || (state.Status != StatusRunning && state.Status != StatusStarting) {
			continue
		}

		tap.Logger(m.ctx).Info("stopping service", "name", name)

		// Check if this is a managed service or process service
        if svcDef, ok := m.serviceDefs[name]; ok {
			// Managed service - call Stop directly
			progress := newProgressReporter(name, tap.Logger(m.ctx))
            var stopErr error
            if svcDef.Hooks != nil && svcDef.Hooks.Stop != nil {
                stopErr = svcDef.Hooks.Stop(m.ctx, progress)
            } else if svcDef.ManagedService != nil {
                stopErr = svcDef.ManagedService.Stop(m.ctx, progress)
            } else {
                stopErr = fmt.Errorf("service %s has no Stop hook or ManagedService", name)
            }
            if stopErr != nil {
                tap.Logger(m.ctx).Error("failed to stop managed service", "name", name, "error", stopErr)
				if firstErr == nil {
                    firstErr = stopErr
				}
			} else {
				state.Status = StatusStopped
				state.PID = 0
			}
		} else {
			// Process service - stop the process directly
			handle, exists := processes[name]
			if !exists {
				state.Status = StatusStopped
				state.PID = 0
				continue
			}

			state.Status = StatusStopping

			// Try graceful shutdown with SIGTERM
			process, err := os.FindProcess(handle.PID)
			if err == nil {
				process.Signal(syscall.SIGTERM)
			}

			// Wait up to 1 second for graceful exit
			select {
			case <-handle.Done:
				tap.Logger(m.ctx).Info("service stopped gracefully", "name", name)
			case <-time.After(1 * time.Second):
				// Force kill
				tap.Logger(m.ctx).Warn("service did not stop gracefully, force killing", "name", name, "pid", handle.PID)
				if err := forceKillProcess(handle.PID); err != nil {
					tap.Logger(m.ctx).Error("failed to force kill process", "name", name, "pid", handle.PID, "error", err)
					if firstErr == nil {
						firstErr = err
					}
				}
				handle.Cancel()
			}
		}
	}

	if firstErr != nil {
		return fmt.Errorf("errors stopping service tree: %w", firstErr)
	}

	tap.Logger(m.ctx).Info("service tree stopped", "root", rootService)
	return nil
}

// findTransitiveDependents finds all services that transitively depend on the given service
func findTransitiveDependents(service string, dependents map[string][]string) []string {
	visited := make(map[string]bool)
	var result []string

	var visit func(string)
	visit = func(svc string) {
		if visited[svc] {
			return
		}
		visited[svc] = true

		for _, dependent := range dependents[svc] {
			visit(dependent)
			result = append(result, dependent)
		}
	}

	visit(service)
	return result
}

// containsString checks if a string slice contains a value
func containsString(slice []string, value string) bool {
	for _, v := range slice {
		if v == value {
			return true
		}
	}
	return false
}

// reverseSlice reverses a string slice
func reverseSlice(slice []string) []string {
	result := make([]string, len(slice))
	for i, v := range slice {
		result[len(slice)-1-i] = v
	}
	return result
}
