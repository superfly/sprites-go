package system

import (
	"context"
	"fmt"
	"time"
)

// Shutdown gracefully shuts down the system in reverse order of startup
// This is the main entry point for stopping the system
func (s *System) Shutdown(shutdownCtx context.Context) error {
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

	// Shutdown order:
	// Phase 1: Prepare container for shutdown (services, process)
	// Phase 2: Unmount overlay filesystem (controlled unmount handles sync)
	// Phase 3: Stop JuiceFS (unmount, stop litestream in JuiceFS)
	// Phase 4: Stop database manager (final litestream sync for metadata DB)
	// Phase 5: Stop network services
	// Phase 6: Stop utilities
	//
	// CRITICAL: Phases 2, 3, and 4 are NOT cancelable via context.
	// They must complete for data integrity, or explicitly error when wedged.
	// The shutdownCtx is only used for informational purposes and phase 1.

	// Phase 1: Prepare container for shutdown (stop services and process)
    if err := s.PrepareContainerForShutdown(shutdownCtx); err != nil {
        // Log and proceed: ServicesManager may not have started yet. Only treat
        // an actively running process that refuses to stop as fatal.
        s.logger.Error("Phase 1 partial failure: container shutdown", "error", err)
        // continue to next phases
    }
	s.logger.Info("Phase 1 complete: Container stopped")

	// Phase 2: Unmount overlay filesystem (MUST happen BEFORE JuiceFS stops)
	// The overlay image file lives on JuiceFS, so overlay must be unmounted first
	// Controlled unmount handles sync properly, no need for separate freeze/sync step
	// Use Background context - this MUST complete for data integrity
	if s.config.OverlayEnabled && s.OverlayManager != nil {
		s.logger.Info("Phase 2: Starting overlay unmount with verification")
		if err := s.UnmountOverlayWithVerification(context.Background()); err != nil {
			s.logger.Error("Phase 2 failed: overlay unmount", "error", err)
			return fmt.Errorf("phase 2 (overlay unmount) failed: %w", err)
		}
		s.logger.Info("Phase 2 complete: Overlay unmounted successfully")
	} else {
		s.logger.Info("Phase 2: Skipping overlay unmount (disabled or not available)")
	}

	// Phase 3: Stop JuiceFS (now safe because overlay is fully unmounted)
	// Use Background context - this MUST complete for data integrity
	// JuiceFS unmount can take up to 5 minutes to flush data to S3
	juicefsStart := time.Now()
	if s.JuiceFS != nil {
		s.logger.Info("Phase 3: Starting JuiceFS shutdown")
		if err := s.JuiceFS.Stop(context.Background()); err != nil {
			s.logger.Error("Phase 3 failed: JuiceFS shutdown", "error", err)
			return fmt.Errorf("phase 3 (JuiceFS shutdown) failed: %w", err)
		}
		s.logger.Info("Phase 3 complete: JuiceFS stopped successfully", "duration", time.Since(juicefsStart))
	} else {
		s.logger.Info("Phase 3: Skipping JuiceFS shutdown (not available)")
	}

	// Phase 4: Stop database manager (final litestream sync for metadata DB)
	// Use Background context - this MUST complete for data integrity
	// Litestream can take up to 1 minute to flush data
	dbStart := time.Now()
	if s.DBManager != nil {
		if err := s.DBManager.Stop(context.Background()); err != nil {
			s.logger.Error("Phase 4 failed: database manager shutdown", "error", err)
			return fmt.Errorf("phase 4 (database manager shutdown) failed: %w", err)
		}
		s.logger.Info("Phase 4 complete: Database manager stopped", "duration", time.Since(dbStart))
	}

	// Phase 5: Stop network services
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	apiErr := s.APIServer.Stop(ctx)
	cancel()
	sockErr := s.SocketServer.Stop()

	if apiErr != nil || sockErr != nil {
		s.logger.Error("Phase 5 failed: network services shutdown", "apiError", apiErr, "sockError", sockErr)
	} else {
		s.logger.Info("Phase 5 complete: Network services stopped")
	}

	// Phase 6: Stop utilities
	adminErr := s.AdminChannel.Stop()
	reaperErr := s.Reaper.Stop(time.Second)

	// Stop resource monitor
	if s.ResourceMonitor != nil {
		s.ResourceMonitor.Stop()
	}

	if adminErr != nil || reaperErr != nil {
		s.logger.Warn("Phase 6 failed: utilities shutdown", "adminError", adminErr, "reaperError", reaperErr)
	} else {
		s.logger.Info("Phase 6 complete: Utilities stopped")
	}

	// Signal shutdown is complete
	close(s.shutdownCompleteCh)

	s.logger.Info("System shutdown complete")
	return nil
}

// PrepareContainerForShutdown stops services and process but does NOT unmount overlay
// This is Phase 1 of shutdown - preparing the container without touching filesystems
func (s *System) PrepareContainerForShutdown(shutdownCtx context.Context) error {
	// Stop services manager first (must stop before container)
	if s.ServicesManager != nil {
		if err := s.ServicesManager.Stop(shutdownCtx); err != nil {
			s.logger.Error("Failed to stop services manager", "error", err)
			// Continue with shutdown even if some services fail to stop
		}
		// Signal services manager fully stopped
		select {
		case <-s.servicesManagerStoppedCh:
			// already closed
		default:
			close(s.servicesManagerStoppedCh)
		}
	}

	// Stop process after services are stopped
	if s.IsProcessRunning() {
		if err := s.StopProcess(); err != nil {
			s.logger.Error("Failed to stop process", "error", err)
			return fmt.Errorf("failed to stop process: %w", err)
		}

		// Wait for process to be completely done
		// This ensures process is no longer using the filesystem
		for i := 0; i < 50; i++ { // Check for up to 5 seconds
			if !s.IsProcessRunning() {
				break
			}
			time.Sleep(100 * time.Millisecond)
		}

		if s.IsProcessRunning() {
			s.logger.Warn("Container process did not stop within timeout")
			return fmt.Errorf("process did not stop within timeout")
		}
	}

	return nil
}

// UnmountOverlayWithVerification unmounts overlay and verifies each step
func (s *System) UnmountOverlayWithVerification(shutdownCtx context.Context) error {
	if s.OverlayManager == nil {
		return nil
	}

	// Unmount overlay (also unmounts checkpoints and both overlayfs and loopback mount)
	if err := s.OverlayManager.Unmount(shutdownCtx); err != nil {
		return fmt.Errorf("failed to unmount overlay: %w", err)
	}

	// Verify both mounts are gone
	if s.OverlayManager.IsOverlayFSMounted() {
		return fmt.Errorf("overlayfs still mounted after unmount")
	}
	if s.OverlayManager.IsMounted() {
		return fmt.Errorf("loopback mount still mounted after unmount")
	}

	return nil
}

// ShutdownContainer stops the container-specific components
// This is used during restore operations to cleanly stop the container environment
// It includes: services manager stop, process stop, and overlay unmount
func (s *System) ShutdownContainer(shutdownCtx context.Context) error {
    s.logger.Info("Starting container shutdown sequence")
    // Prevent monitor-triggered full shutdown during container-only maintenance
    s.userEnvMaintenance.Store(true)
    defer s.userEnvMaintenance.Store(false)

	// Phase 1: Stop services manager first (must stop before container)
	s.logger.Info("Phase 1: Stopping services manager")
	if s.ServicesManager != nil {
		if err := s.ServicesManager.Stop(shutdownCtx); err != nil {
			s.logger.Error("Failed to stop services manager", "error", err)
			// Continue with shutdown even if some services fail to stop
		} else {
			s.logger.Info("Services manager stopped")
			// Signal services manager fully stopped
			select {
			case <-s.servicesManagerStoppedCh:
				// already closed
			default:
				close(s.servicesManagerStoppedCh)
			}
		}
	}

	// Phase 2: Stop process after services are stopped
	s.logger.Info("Phase 2: Stopping container process")
	if s.IsProcessRunning() {
		if err := s.StopProcess(); err != nil {
			s.logger.Error("Failed to stop process", "error", err)
			return fmt.Errorf("failed to stop container process: %w", err)
		}
		s.logger.Info("Container process fully stopped")
	} else {
		s.logger.Info("No process running to stop")
	}

	// Phase 3: Unmount overlay filesystem
	// Use Background context - this MUST complete for data integrity
	s.logger.Info("Phase 3: Unmounting overlay filesystem")
	if s.config.OverlayEnabled && s.OverlayManager != nil {
		if err := s.UnmountOverlayWithVerification(context.Background()); err != nil {
			s.logger.Error("Failed to unmount overlay", "error", err)
			return fmt.Errorf("failed to unmount overlay: %w", err)
		}
		s.logger.Info("Overlay unmounted successfully")
	}

	s.logger.Info("Container shutdown sequence completed")
	return nil
}
