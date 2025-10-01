package system

import (
	"context"
	"fmt"
	"os"
	"os/signal"
	"syscall"
)

// Boot starts the system and all its modules in the correct order
// This is the main entry point for starting the system
func (s *System) Boot(ctx context.Context) error {
	s.logger.Info("Starting system boot sequence", "system_ptr", fmt.Sprintf("%p", s))

	// Mark system as running
	s.mu.Lock()
	if s.running {
		s.mu.Unlock()
		return fmt.Errorf("system already running")
	}
	s.running = true
	s.mu.Unlock()

	// Phase 1: Start utilities (no dependencies)
	s.logger.Info("Phase 1: Starting utilities")
	s.Reaper.Start()
	s.logger.Info("Zombie reaper started")

	if err := s.AdminChannel.Start(); err != nil {
		s.logger.Error("Failed to start admin channel", "error", err)
		// Non-fatal, continue without admin channel
	} else {
		s.logger.Info("Admin channel started")
	}

	s.ResourceMonitor.Start(s.ctx)
	s.logger.Info("Resource monitor started")

	// Phase 2: Start network services early (can accept connections while rest boots)
	s.logger.Info("Phase 2: Starting network services")

	// Start API server if configured
	if s.config.APIListenAddr != "" {
		go func() {
			if err := s.APIServer.Start(); err != nil {
				s.logger.Error("API server error", "error", err)
				// Just log the error, don't trigger shutdown
				// The operator should handle this via monitoring
			}
		}()
		s.logger.Info("API server started")
	}

	// Start socket server for services API
	socketPath := "/tmp/sprite.sock"
	if err := s.SocketServer.Start(socketPath); err != nil {
		s.logger.Error("Failed to start socket server", "error", err)
		// Non-fatal, services API will not be available
	} else {
		s.logger.Info("Socket server started", "path", socketPath)
	}

	// Wait for boot signal if configured
	if os.Getenv("WAIT_FOR_BOOT") == "true" {
		s.logger.Info("WAIT_FOR_BOOT enabled, HTTP server is listening, waiting for SIGUSR1...")
		sigCh := make(chan os.Signal, 1)
		signal.Notify(sigCh, syscall.SIGUSR1)
		<-sigCh
		signal.Stop(sigCh) // Stop receiving on this channel
		s.logger.Info("Received SIGUSR1, continuing boot...")
	}

	// Phase 3: Start storage components in order
	// Note: /dev/fly_vol mount and checkpoint migration happen in main.go before system creation
	s.logger.Info("Phase 3: Starting storage components")

	// Database manager
	if err := s.DBManager.Start(s.ctx); err != nil {
		return fmt.Errorf("failed to start database manager: %w", err)
	}
	s.logger.Info("Database manager started")

	// JuiceFS (depends on DB)
	if s.config.JuiceFSDataPath != "" {
		s.logger.Info("Starting JuiceFS", "juiceFS_ptr", fmt.Sprintf("%p", s.JuiceFS))
		// JuiceFS.Start() blocks until mount is ready
		if err := s.JuiceFS.Start(s.ctx); err != nil {
			return fmt.Errorf("failed to start JuiceFS: %w", err)
		}
		s.logger.Info("JuiceFS started and mounted")

		// Special wait point after JuiceFS is ready
		if os.Getenv("WAIT_FOR_JUICEFS_READY") == "true" {
			s.logger.Info("WAIT_FOR_JUICEFS_READY enabled, JuiceFS is ready, waiting for SIGUSR1...")
			sigCh := make(chan os.Signal, 1)
			signal.Notify(sigCh, syscall.SIGUSR1)
			<-sigCh
			signal.Stop(sigCh)
			s.logger.Info("Received SIGUSR1, continuing...")
		}
	}

	// Overlay manager (depends on JuiceFS)
	if s.config.OverlayEnabled {
		s.logger.Info("Starting overlay manager")
		// Mount() should block until overlay is ready
		if err := s.OverlayManager.Mount(s.ctx); err != nil {
			return fmt.Errorf("failed to mount overlay: %w", err)
		}
		s.logger.Info("Overlay mounted")
	}

	// Phase 4: Start process if configured
	if len(s.config.ProcessCommand) > 0 {
		s.logger.Info("Phase 4: Starting container process")
		if err := s.StartProcess(); err != nil {
			return fmt.Errorf("failed to start process: %w", err)
		}
	}

	// Phase 5: Start services manager (depends on container being running)
	s.logger.Info("Phase 5: Starting services manager")
	if err := s.ServicesManager.Start(); err != nil {
		return fmt.Errorf("failed to start services manager: %w", err)
	}
	s.logger.Info("Services manager started")

	// Phase 6: Start activity monitor (after process starts)
	s.logger.Info("Phase 6: Starting activity monitor")
	s.ActivityMonitor.Start(s.ctx)

	// Configure activity monitoring for API server
	if s.config.APIListenAddr != "" {
		s.APIServer.SetActivityObserver(func(start bool) {
			if start {
				s.ActivityMonitor.ActivityStarted("http")
			} else {
				s.ActivityMonitor.ActivityEnded("http")
			}
		})
	}

	// Set up tmux activity monitoring
	s.setupTmuxActivityMonitoring()

	s.logger.Info("Activity monitor started")

	s.logger.Info("System boot complete")
	return nil
}

// setupTmuxActivityMonitoring configures tmux activity tracking
func (s *System) setupTmuxActivityMonitoring() {
	s.logger.Info("Setting up tmux activity monitor prepare command")

	s.TMUXManager.SetPrepareCommand(func() {
		// Start the tmux activity monitor
		s.logger.Info("Prepare command executing - starting tmux activity monitor")

		if err := s.TMUXManager.StartActivityMonitor(s.ctx); err != nil {
			s.logger.Warn("Failed to start tmux activity monitor", "error", err)
		} else {
			s.logger.Info("Successfully started tmux activity monitor")
		}
	})

	// Connect tmux activity events to the activity monitor
	go func() {
		s.logger.Info("Starting tmux activity event forwarder")
		activityChan := s.TMUXManager.GetActivityChannel()
		for {
			select {
			case <-s.ctx.Done():
				s.logger.Debug("Tmux activity forwarder stopped due to context cancellation")
				return
			case tmuxActivity, ok := <-activityChan:
				if !ok {
					s.logger.Error("Tmux activity channel closed unexpectedly")
					return
				}

				s.logger.Debug("Received tmux activity event",
					"sessionID", tmuxActivity.SessionID,
					"active", tmuxActivity.Active,
					"type", tmuxActivity.Type)

				// Forward to activity monitor
				if tmuxActivity.Active {
					s.ActivityMonitor.ActivityStarted("tmux")
				} else {
					s.ActivityMonitor.ActivityEnded("tmux")
				}
			}
		}
	}()
}

// BootContainer starts the container-specific components after JuiceFS is ready
// This is used during restore operations to boot the container environment
// It includes: overlay mount, process start, and services manager start
func (s *System) BootContainer(ctx context.Context) error {
	s.logger.Info("Starting container boot sequence")

	// Phase 1: Mount overlay filesystem (depends on JuiceFS)
	if s.config.OverlayEnabled {
		s.logger.Info("Phase 1: Mounting overlay filesystem")
		// Update the image path to point to the restored active directory
		s.OverlayManager.UpdateImagePath()

		// Mount() should block until overlay is ready
		if err := s.OverlayManager.Mount(ctx); err != nil {
			return fmt.Errorf("failed to mount overlay: %w", err)
		}
		s.logger.Info("Overlay mounted successfully")
	}

	// Phase 2: Start process if configured
	if len(s.config.ProcessCommand) > 0 {
		s.logger.Info("Phase 2: Starting container process")
		if err := s.StartProcess(); err != nil {
			return fmt.Errorf("failed to start process: %w", err)
		}
		s.logger.Info("Container process started")
	}

	// Phase 3: Start services manager (depends on container being running)
	s.logger.Info("Phase 3: Starting services manager")
	if err := s.ServicesManager.Start(); err != nil {
		return fmt.Errorf("failed to start services manager: %w", err)
	}
	s.logger.Info("Services manager started")

	// Flip services manager stopped channel to running (open channel)
	s.servicesManagerStoppedCh = make(chan struct{})

	// Phase 4: Start all services automatically
	s.logger.Info("Phase 4: Starting all services")
	if err := s.ServicesManager.StartAll(); err != nil {
		s.logger.Error("Failed to start services", "error", err)
		// Non-fatal error, container boot is still successful
	} else {
		s.logger.Info("All services started successfully")
	}

	s.logger.Info("Container boot sequence completed")
	return nil
}
