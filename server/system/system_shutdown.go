package system

import (
	"context"
	"fmt"
	"os"
	"time"
)

// Shutdown gracefully shuts down the system in reverse order of startup
// This is the main entry point for stopping the system
func (s *System) Shutdown(shutdownCtx context.Context) error {
	// Ensure any safety timer is stopped when Shutdown returns
	var safetyTimer *time.Timer
	defer func() {
		if safetyTimer != nil {
			safetyTimer.Stop()
		}
	}()
	// Emit shutdown start event
	s.emitAdminEvent("shutdown.start", map[string]interface{}{
		"status":     "start",
		"started_at": time.Now().UnixMilli(),
	})
	// Get deadline from context if available
	deadline, hasDeadline := shutdownCtx.Deadline()
	if hasDeadline {
		s.logger.Info("Starting system shutdown sequence",
			"system_ptr", fmt.Sprintf("%p", s),
			"deadline", deadline,
			"timeout", time.Until(deadline))
	} else {
		s.logger.Info("Starting system shutdown sequence",
			"system_ptr", fmt.Sprintf("%p", s),
			"deadline", "none")
	}

	// Mark system as stopping
	s.mu.Lock()
	if !s.running {
		s.mu.Unlock()
		s.logger.Info("System already stopped")
		return nil
	}
	s.running = false
	s.mu.Unlock()

	// Broadcast shutdown to all goroutines that observe this channel
	s.shutdownTriggeredOnce.Do(func() {
		close(s.shutdownTriggeredCh)
	})

	// Wait for any in-progress Boot() step to complete before proceeding
	// This gates Phase 2/3 so we don't race with boot continuing to mount overlay, etc.
	s.logger.Debug("Waiting for boot to finish current step before shutdown phases")
	<-s.bootDoneCh
	s.logger.Debug("Boot finished; proceeding with shutdown phases")

	// Immediately stop the activity monitor to prevent suspend during shutdown
	if s.ActivityMonitor != nil {
		s.ActivityMonitor.Stop()
	}

	// DO NOT cancel the system context here - let components finish their work
	// Components should respect the shutdownCtx passed to them

	// Use the unified service manager to stop all services in reverse dependency order
	// This handles: services_manager → container → overlay → juicefs → db_manager → utilities
	s.logger.Info("Stopping all services using unified service manager")

	// Use background context for critical data integrity operations (juicefs, db)
	// The service wrappers will use this for Stop()
	shutdownStart := time.Now()
	if err := s.UnifiedServiceManager.Shutdown(); err != nil {
		s.logger.Error("Unified service manager shutdown failed", "error", err)
		// Continue with cleanup
	}
	s.logger.Info("All services stopped via unified manager", "duration", time.Since(shutdownStart))

	// Safety: ensure JuiceFS is fully stopped even if service state wasn't marked running
	if s.JuiceFS != nil {
		if s.JuiceFS.IsMounted() {
			s.logger.Warn("JuiceFS still mounted after manager shutdown; stopping explicitly for cleanup")
			_ = s.JuiceFS.Stop(context.Background())
		}
	}

	// Async admin channel leave (best effort)
	if s.AdminChannel != nil {
		s.AdminChannel.LeaveAsync()
	}

	// Stop resource monitor (not in unified manager yet)
	if s.ResourceMonitor != nil {
		s.ResourceMonitor.Stop()
	}

	// Safety valve: if anything hangs after critical services stopped, force exit
	safetyTimer = time.AfterFunc(5*time.Second, func() {
		s.logger.Info("Forcing process exit after shutdown grace period")
		os.Exit(0)
	})

	// Signal shutdown is complete
	close(s.shutdownCompleteCh)

	// Emit shutdown completion event
	s.emitAdminEvent("shutdown.complete", map[string]interface{}{
		"status":      "ok",
		"finished_at": time.Now().UnixMilli(),
	})
	s.logger.Info("System shutdown complete")
	return nil
}

// ShutdownContainer stops the container-specific components
// This is used during restore operations to cleanly stop the container environment
// It uses the unified service manager to stop the container service tree
func (s *System) ShutdownContainer(shutdownCtx context.Context) error {
	s.logger.Info("Starting container shutdown sequence using unified service manager")
	// Prevent monitor-triggered full shutdown during container-only maintenance
	s.userEnvMaintenance.Store(true)
	defer s.userEnvMaintenance.Store(false)

	// Stop dependents of container first (e.g. services_manager), then container itself
	if err := s.UnifiedServiceManager.StopServiceTree("container"); err != nil {
		s.logger.Error("Failed to stop container service tree", "error", err)
		return fmt.Errorf("failed to stop container: %w", err)
	}

	// Then explicitly stop overlay and any dependents above it (none after container)
	// Overlay is a dependency of container, not a dependent, so it is NOT stopped
	// by stopping the container tree. We stop it explicitly to match prior behavior.
	if s.config.OverlayEnabled {
		if err := s.UnifiedServiceManager.StopServiceTree("overlay"); err != nil {
			s.logger.Error("Failed to stop overlay service tree", "error", err)
			return fmt.Errorf("failed to stop overlay: %w", err)
		}
	}

	s.logger.Info("Container shutdown sequence completed")
	return nil
}
