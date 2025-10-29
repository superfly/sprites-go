package system

import (
	"context"
	"fmt"
	"time"
)

// Boot starts the system and all its modules in the correct order
// This is the main entry point for starting the system
func (s *System) Boot(ctx context.Context) error {
	// Ensure bootDoneCh is closed on any return so Shutdown can proceed
	defer func() {
		select {
		case <-s.bootDoneCh:
			// already closed
		default:
			close(s.bootDoneCh)
		}
	}()
	s.logger.Info("Starting system boot sequence using unified service manager", "system_ptr", fmt.Sprintf("%p", s))

	// Emit boot start event
	s.emitAdminEvent("boot.start", map[string]interface{}{
		"status":     "start",
		"started_at": time.Now().UnixMilli(),
	})

	// Mark system as running
	s.mu.Lock()
	if s.running {
		s.mu.Unlock()
		return fmt.Errorf("system already running")
	}
	s.running = true
	s.mu.Unlock()

	// Register all system services with the unified manager
	s.logger.Info("Registering system services")
	if err := s.registerSystemServices(); err != nil {
		return fmt.Errorf("failed to register system services: %w", err)
	}

	// Start all services in parallel by dependency level
	s.logger.Info("Starting all services using unified service manager")
	if err := s.UnifiedServiceManager.StartAll(); err != nil {
		return fmt.Errorf("failed to start services: %w", err)
	}

	// Post-boot hooks that need to run after specific services
	// Move litestream process to its cgroup (after db_manager starts)
	if s.DBManager != nil {
		if litestreamPid := s.DBManager.GetLitestreamPid(); litestreamPid > 0 {
			if err := MovePid(litestreamPid, "litestream"); err != nil {
				s.logger.Warn("Failed to move litestream process to cgroup", "error", err, "pid", litestreamPid)
			} else {
				s.logger.Info("Moved litestream process to cgroup", "pid", litestreamPid)
			}
		}
	}

	// Move juicefs process to its cgroup (after juicefs starts)
	if s.JuiceFS != nil {
		if juicefsPid := s.JuiceFS.GetPid(); juicefsPid > 0 {
			if err := MovePid(juicefsPid, "juicefs"); err != nil {
				s.logger.Warn("Failed to move juicefs process to cgroup", "error", err, "pid", juicefsPid)
			} else {
				s.logger.Info("Moved juicefs process to cgroup", "pid", juicefsPid)
			}
		}
	}

	// Initialize sprite database schema (after db_manager starts)
	s.logger.Info("Initializing sprite database schema")
	if err := s.InitializeSpriteDB(s.ctx); err != nil {
		s.logger.Warn("Failed to initialize sprite database schema", "error", err)
		// Non-fatal
	} else {
		s.logger.Info("Sprite database schema initialized")
	}

	// Network policy is now managed by the unified service manager

	// Apply sprite hostname if assigned (after container is running)
	if info, err := s.GetSpriteInfo(s.ctx); err == nil && info != nil {
		s.logger.Info("Applying sprite hostname", "sprite_name", info.SpriteName)
		if err := s.ApplySpriteHostname(s.ctx, info.SpriteName); err != nil {
			s.logger.Warn("Failed to apply sprite hostname", "error", err)
			// Non-fatal
		}
	}

	// Emit boot completion
	s.emitAdminEvent("boot.complete", map[string]interface{}{
		"status":      "ok",
		"finished_at": time.Now().UnixMilli(),
	})
	s.ActivityMonitor.ActivityEnded("boot")
	s.logger.Info("System boot complete")
	return nil
}

// BootContainer starts the container-specific components after JuiceFS is ready
// This is used during restore operations to boot the container environment
// Uses UnifiedServiceManager to restart the container service tree
// PREREQUISITE: SystemBoot must be running (JuiceFS, DBManager) - call Start() first
func (s *System) BootContainer(ctx context.Context) error {
	s.logger.Info("Starting container boot sequence using unified service manager")
	// Prevent monitor-triggered full shutdown during container-only maintenance
	s.userEnvMaintenance.Store(true)
	defer s.userEnvMaintenance.Store(false)

	// Validate that SystemBoot is running
	if s.JuiceFS != nil && !s.JuiceFS.IsMounted() {
		return fmt.Errorf("cannot boot container: JuiceFS is not mounted")
	}
	if s.DBManager == nil {
		return fmt.Errorf("cannot boot container: DBManager is not initialized")
	}

	// Start the container service tree via UnifiedServiceManager
	// StartServiceTree will start overlay → container → services_manager in correct order
	s.logger.Info("Restarting container services via StartServiceTree")
	if err := s.UnifiedServiceManager.StartServiceTree("services_manager"); err != nil {
		return fmt.Errorf("failed to start container services: %w", err)
	}

	// Apply sprite hostname if needed
	if info, err := s.GetSpriteInfo(ctx); err == nil && info != nil {
		s.logger.Info("Applying sprite hostname", "sprite_name", info.SpriteName)
		if err := s.ApplySpriteHostname(ctx, info.SpriteName); err != nil {
			s.logger.Warn("Failed to apply sprite hostname", "error", err)
		}
	}

	s.logger.Info("Container boot sequence completed")
	return nil
}
