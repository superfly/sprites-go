package services

import (
	"context"
	"fmt"
	"os"
	"sync"
	"syscall"
	"time"

	"github.com/superfly/sprite-env/pkg/tap"
)

// handleShutdownInternal stops all services in reverse dependency order
// Works with both BaseManager (serviceDefs only) and PersistentManager (serviceDefs + db)
func handleShutdownInternal(
	ctx context.Context,
	serviceDefs map[string]*ServiceDefinition,
	db *DB, // optional, can be nil
	states map[string]*ServiceState,
	processes map[string]*ProcessHandle,
) error {
	// Collect all services from serviceDefs and optionally from database
	deps := make(map[string][]string)
	allServiceNames := make([]string, 0)

	// Add registered service definitions (managed services)
	for name, svcDef := range serviceDefs {
		deps[name] = svcDef.Dependencies
		allServiceNames = append(allServiceNames, name)
	}

	// Add database services if database is available
	if db != nil {
		allServices, err := db.ListServices()
		if err == nil {
			for _, svc := range allServices {
				// Only add if not already registered as a ServiceDefinition
				if _, exists := serviceDefs[svc.Name]; !exists {
					deps[svc.Name] = svc.Needs
					allServiceNames = append(allServiceNames, svc.Name)
				}
			}
		}
	}

	if len(allServiceNames) == 0 {
		tap.Logger(ctx).Info("no services to shutdown")
		return nil
	}

	// Build reverse dependency map
	dependents := make(map[string][]string)
	for name, dependencies := range deps {
		for _, dep := range dependencies {
			dependents[dep] = append(dependents[dep], name)
		}
	}

	// Calculate shutdown order
	shutdownOrder := calculateShutdownOrderFromDeps(allServiceNames, dependents)

	// Group by dependency level for parallel shutdown
	levels := groupByDependencyLevelFromNames(shutdownOrder, deps)

	tap.Logger(ctx).Info("shutting down services", "total", len(shutdownOrder))
	tap.Logger(ctx).Info("shutdown order (by level)", "levels", levels)

	// Shutdown each level in reverse order, services within a level in parallel
	for i := len(levels) - 1; i >= 0; i-- {
		level := levels[i]
		if len(level) == 0 {
			continue
		}

		tap.Logger(ctx).Info("shutting down service level", "level", i, "services", level)

		var wg sync.WaitGroup
		for _, svcName := range level {
			state, exists := states[svcName]
			if !exists || (state.Status != StatusRunning && state.Status != StatusStarting) {
				tap.Logger(ctx).Debug("skipping service (not running)", "name", svcName, "exists", exists)
				if exists {
					tap.Logger(ctx).Debug("service status", "name", svcName, "status", state.Status)
				}
				continue
			}

			wg.Add(1)
			go func(name string) {
				defer wg.Done()
				tap.Logger(ctx).Info("BEGIN stopping service", "name", name, "level", i)

				// Check if this is a managed service or process service
				if svcDef, ok := serviceDefs[name]; ok {
					// Managed service
					tap.Logger(ctx).Info("stopping managed service", "name", name)

					progress := newProgressReporter(name, tap.Logger(ctx))

                    var stopErr error
                    if svcDef.Hooks != nil && svcDef.Hooks.Stop != nil {
                        stopErr = svcDef.Hooks.Stop(ctx, progress)
                    } else if svcDef.ManagedService != nil {
                        stopErr = svcDef.ManagedService.Stop(ctx, progress)
                    } else {
                        stopErr = fmt.Errorf("service %s has no Stop hook or ManagedService", name)
                    }
                    if stopErr != nil {
                        tap.Logger(ctx).Error("failed to stop managed service", "name", name, "error", stopErr)
						if s, ok := states[name]; ok {
							s.Status = StatusFailed
						}
					} else {
						if s, ok := states[name]; ok {
							s.Status = StatusStopped
							s.PID = 0
						}
						tap.Logger(ctx).Info("managed service stopped", "name", name)
					}
					tap.Logger(ctx).Info("DONE stopping service", "name", name, "level", i)
				} else {
					// Process service
					handle, exists := processes[name]
					if !exists {
						return
					}

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
						tap.Logger(ctx).Info("process service stopped gracefully", "name", name)
					case <-time.After(1 * time.Second):
						tap.Logger(ctx).Warn("process service did not stop gracefully, force killing", "name", name, "pid", handle.PID)
						if err := forceKillProcess(handle.PID); err != nil {
							tap.Logger(ctx).Error("failed to force kill process", "name", name, "pid", handle.PID, "error", err)
						}
						handle.Cancel()
					}
					tap.Logger(ctx).Info("DONE stopping service", "name", name, "level", i)
				}
			}(svcName)
		}

		tap.Logger(ctx).Info("waiting for service level to complete", "level", i, "count", len(level))
		wg.Wait()
		tap.Logger(ctx).Info("service level complete", "level", i)
	}

	return nil
}

// handleStopServiceTreeInternal stops a service and all its dependents
func handleStopServiceTreeInternal(
	ctx context.Context,
	serviceDefs map[string]*ServiceDefinition,
	db *DB,
	rootService string,
	states map[string]*ServiceState,
	processes map[string]*ProcessHandle,
) error {
	// Build dependency tree
	dependents := make(map[string][]string)

	// From service definitions
	for name, svcDef := range serviceDefs {
		for _, dep := range svcDef.Dependencies {
			dependents[dep] = append(dependents[dep], name)
		}
	}

	// From database if available
	if db != nil {
		services, err := db.ListServices()
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
	stopOrder := append(toStop, rootService)

	tap.Logger(ctx).Info("stopping service tree", "root", rootService, "total", len(stopOrder))

	// Stop each service in order
	var firstErr error
	for _, name := range stopOrder {
		state, exists := states[name]
		if !exists || (state.Status != StatusRunning && state.Status != StatusStarting) {
			continue
		}

		tap.Logger(ctx).Info("stopping service", "name", name)

		// Check if managed or process service
		if svcDef, ok := serviceDefs[name]; ok {
			// Managed service
			progress := newProgressReporter(name, tap.Logger(ctx))
            var stopErr error
            if svcDef.Hooks != nil && svcDef.Hooks.Stop != nil {
                stopErr = svcDef.Hooks.Stop(ctx, progress)
            } else if svcDef.ManagedService != nil {
                stopErr = svcDef.ManagedService.Stop(ctx, progress)
            } else {
                stopErr = fmt.Errorf("service %s has no Stop hook or ManagedService", name)
            }
            if stopErr != nil {
                tap.Logger(ctx).Error("failed to stop managed service", "name", name, "error", stopErr)
				if firstErr == nil {
                    firstErr = stopErr
				}
			} else {
				state.Status = StatusStopped
				state.PID = 0
			}
		} else {
			// Process service
			handle, exists := processes[name]
			if !exists {
				state.Status = StatusStopped
				state.PID = 0
				continue
			}

			state.Status = StatusStopping

			process, err := os.FindProcess(handle.PID)
			if err == nil {
				process.Signal(syscall.SIGTERM)
			}

			select {
			case <-handle.Done:
				tap.Logger(ctx).Info("service stopped gracefully", "name", name)
			case <-time.After(1 * time.Second):
				tap.Logger(ctx).Warn("service did not stop gracefully, force killing", "name", name, "pid", handle.PID)
				if err := forceKillProcess(handle.PID); err != nil {
					tap.Logger(ctx).Error("failed to force kill process", "name", name, "pid", handle.PID, "error", err)
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

	tap.Logger(ctx).Info("service tree stopped", "root", rootService)
	return nil
}
