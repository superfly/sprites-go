package services

import (
	"fmt"
	"os"
	"sync"
	"syscall"
	"time"

	"github.com/superfly/sprite-env/pkg/tap"
)

// handleShutdown stops all services in reverse dependency order
func (m *Manager) handleShutdown(states map[string]*ServiceState, processes map[string]*ProcessHandle) error {
	// Ensure database is initialized
	if err := m.ensureDB(); err != nil {
		return fmt.Errorf("failed to initialize database: %w", err)
	}

	// Get all services
	allServices, err := m.db.ListServices()
	if err != nil {
		return fmt.Errorf("failed to list services: %w", err)
	}

	// Build dependency map
	dependents := make(map[string][]string)
	for _, svc := range allServices {
		for _, dep := range svc.Needs {
			dependents[dep] = append(dependents[dep], svc.Name)
		}
	}

	// Calculate shutdown order (reverse dependency order)
	shutdownOrder := m.calculateShutdownOrder(allServices, dependents)

	tap.Logger(m.ctx).Info("shutting down services", "order", shutdownOrder)

	// Group services by level for parallel shutdown
	levels := m.groupByDependencyLevel(shutdownOrder, allServices)

	// Shutdown each level in sequence, but services within a level in parallel
	for i := len(levels) - 1; i >= 0; i-- {
		level := levels[i]
		if len(level) == 0 {
			continue
		}

		var wg sync.WaitGroup
		for _, svcName := range level {
			state, exists := states[svcName]
			if !exists || state.Status != StatusRunning {
				continue
			}

			wg.Add(1)
			go func(name string) {
				defer wg.Done()

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
					tap.Logger(m.ctx).Info("service stopped gracefully", "name", name)
				case <-time.After(1 * time.Second):
					// Force kill
					tap.Logger(m.ctx).Warn("service did not stop gracefully, force killing", "name", name, "pid", handle.PID)
					if err := forceKillProcess(handle.PID); err != nil {
						tap.Logger(m.ctx).Error("failed to force kill process", "name", name, "pid", handle.PID, "error", err)
					}
					// Cancel context to clean up
					handle.Cancel()
				}
			}(svcName)
		}

		// Wait for this level to complete
		wg.Wait()
	}

	return nil
}
