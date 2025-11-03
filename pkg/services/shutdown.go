package services

import (
	"os"
	"sync"
	"syscall"
	"time"

	"github.com/superfly/sprite-env/pkg/tap"
)

// handleShutdown stops all services in reverse dependency order
func (m *Manager) handleShutdown(states map[string]*ServiceState, processes map[string]*ProcessHandle) error {
	// Collect all services from both serviceDefs and database
	deps := make(map[string][]string)
	allServiceNames := make([]string, 0)

	// Add registered service definitions (managed services)
	for name, svcDef := range m.serviceDefs {
		deps[name] = svcDef.Dependencies
		allServiceNames = append(allServiceNames, name)
	}

	// Add database services (process-based services) if database is available
	if m.db != nil {
		allServices, err := m.db.ListServices()
		if err == nil {
			for _, svc := range allServices {
				// Only add if not already registered as a ServiceDefinition
				if _, exists := m.serviceDefs[svc.Name]; !exists {
					deps[svc.Name] = svc.Needs
					allServiceNames = append(allServiceNames, svc.Name)
				}
			}
		}
	}

	if len(allServiceNames) == 0 {
		tap.Logger(m.ctx).Info("no services to shutdown")
		return nil
	}

	// Build reverse dependency map (dependents)
	dependents := make(map[string][]string)
	for name, dependencies := range deps {
		for _, dep := range dependencies {
			dependents[dep] = append(dependents[dep], name)
		}
	}

	// Calculate shutdown order (stop dependents before dependencies)
	shutdownOrder := calculateShutdownOrderFromDeps(allServiceNames, dependents)

	// Group by dependency level for parallel shutdown within levels
	levels := groupByDependencyLevelFromNames(shutdownOrder, deps)

	tap.Logger(m.ctx).Info("shutting down services", "total", len(shutdownOrder))
	tap.Logger(m.ctx).Info("shutdown order (by level)", "levels", levels)

	// Shutdown each level in reverse order, services within a level in parallel
	for i := len(levels) - 1; i >= 0; i-- {
		level := levels[i]
		if len(level) == 0 {
			continue
		}

		tap.Logger(m.ctx).Info("shutting down service level", "level", i, "services", level)

		var wg sync.WaitGroup
		for _, svcName := range level {
			state, exists := states[svcName]
			if !exists || (state.Status != StatusRunning && state.Status != StatusStarting) {
				tap.Logger(m.ctx).Debug("skipping service (not running)", "name", svcName, "exists", exists)
				if exists {
					tap.Logger(m.ctx).Debug("service status", "name", svcName, "status", state.Status)
				}
				continue
			}

			wg.Add(1)
			go func(name string) {
				defer wg.Done()
				tap.Logger(m.ctx).Info("BEGIN stopping service", "name", name, "level", i)

				// Check if this is a managed service or process service
				if svcDef, ok := m.serviceDefs[name]; ok {
					// Managed service - call Stop directly (we're already in the event loop)
					tap.Logger(m.ctx).Info("stopping managed service", "name", name)

					// Create progress reporter
					progress := newProgressReporter(name, tap.Logger(m.ctx))

					// Call Stop directly without the monitoring wrapper
					if err := svcDef.ManagedService.Stop(m.ctx, progress); err != nil {
						tap.Logger(m.ctx).Error("failed to stop managed service", "name", name, "error", err)
						// Update state to failed
						if s, ok := states[name]; ok {
							s.Status = StatusFailed
						}
					} else {
						// Update state to stopped
						if s, ok := states[name]; ok {
							s.Status = StatusStopped
							s.PID = 0
						}
						tap.Logger(m.ctx).Info("managed service stopped", "name", name)
					}
					tap.Logger(m.ctx).Info("DONE stopping service", "name", name, "level", i)
				} else {
					// Process service - stop the process
					handle, exists := processes[name]
					if !exists {
						return
					}

					// Update state
					if s, ok := states[name]; ok {
						s.Status = StatusStopping
					}

					// Try graceful shutdown with SIGTERM
					process, err := os.FindProcess(handle.PID)
					if err == nil {
						process.Signal(syscall.SIGTERM)
					}

					// Wait up to 1 second for graceful exit
					select {
					case <-handle.Done:
						tap.Logger(m.ctx).Info("process service stopped gracefully", "name", name)
					case <-time.After(1 * time.Second):
						// Force kill
						tap.Logger(m.ctx).Warn("process service did not stop gracefully, force killing", "name", name, "pid", handle.PID)
						if err := forceKillProcess(handle.PID); err != nil {
							tap.Logger(m.ctx).Error("failed to force kill process", "name", name, "pid", handle.PID, "error", err)
						}
						// Cancel context to clean up
						handle.Cancel()
					}
					tap.Logger(m.ctx).Info("DONE stopping service", "name", name, "level", i)
				}
			}(svcName)
		}

		// Wait for all services at this level to complete
		tap.Logger(m.ctx).Info("waiting for service level to complete", "level", i, "count", len(level))
		wg.Wait()
		tap.Logger(m.ctx).Info("service level complete", "level", i)
	}

	return nil
}

// groupByDependencyLevelFromNames groups services by dependency level using deps map
func groupByDependencyLevelFromNames(serviceNames []string, deps map[string][]string) [][]string {
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
	for _, name := range serviceNames {
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

// calculateShutdownOrderFromDeps calculates the order to stop services
// Services that depend on others are stopped first (reverse dependency order)
func calculateShutdownOrderFromDeps(allServices []string, dependents map[string][]string) []string {
	visited := make(map[string]bool)
	order := []string{}

	var visit func(name string)
	visit = func(name string) {
		if visited[name] {
			return
		}
		visited[name] = true

		// Visit all services that depend on this one first
		for _, dependent := range dependents[name] {
			visit(dependent)
		}

		order = append(order, name)
	}

	// Visit all services
	for _, name := range allServices {
		visit(name)
	}

	// The DFS already puts dependents before dependencies, so NO reversal needed
	// order is already: [services_manager, container, overlay, juicefs, db_manager, ...]
	return order
}
