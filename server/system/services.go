package system

import (
	"fmt"
	"time"

	"github.com/superfly/sprite-env/pkg/services"
	"github.com/superfly/sprite-env/pkg/terminal"
)

// initializeServices initializes service components
func (s *System) initializeServices() error {
	// Initialize services manager
	if err := s.initializeServicesManager(); err != nil {
		return fmt.Errorf("failed to initialize services manager: %w", err)
	}

	// Initialize TMUX manager
	if err := s.initializeTMUXManager(); err != nil {
		// Non-fatal - continue without terminal management
		s.logger.Warn("Failed to initialize TMUX manager", "error", err)
	}

	// Initialize activity monitor
	s.initializeActivityMonitor()

	return nil
}

// initializeServicesManager creates the services manager
func (s *System) initializeServicesManager() error {
	servicesDataPath := "/mnt/user-data"

	// Always create services manager
	servicesManager, err := services.NewManager(servicesDataPath,
		services.WithLogDir(s.config.LogDir))
	if err != nil {
		return err
	}

	// Set command prefix if configured
	if len(s.config.ExecWrapperCommand) > 0 {
		servicesManager.SetCmdPrefix(s.config.ExecWrapperCommand)
	}

	s.ServicesManager = servicesManager
	return nil
}

// initializeTMUXManager creates the TMUX manager
func (s *System) initializeTMUXManager() error {
	// Always create TMUX manager
	tmuxManager := terminal.NewTMUXManager(s.ctx)

	// Set command prefix if configured
	if len(s.config.ExecWrapperCommand) > 0 {
		tmuxManager.SetCmdPrefix(s.config.ExecWrapperCommand)
	}

	s.TMUXManager = tmuxManager
	return nil
}

// initializeActivityMonitor creates the activity monitor
func (s *System) initializeActivityMonitor() {
	// Always create activity monitor with 30 second idle timeout
	s.ActivityMonitor = NewActivityMonitor(s.ctx, s, 30*time.Second)
	s.ActivityMonitor.SetAdminChannel(s.AdminChannel)

	// Initialize resource monitor on Linux (no-op on other platforms)
	s.initializeResourceMonitor()
}

// initializeResourceMonitor creates the resource monitor (Linux only)
func (s *System) initializeResourceMonitor() {
	// Create a callback that safely forwards metrics to the admin channel
	// The admin channel may not be connected yet, but will be during Boot()
	metricsCallback := func(metrics interface{}) {
		// The new Push method handles nil checking and payload conversion
		s.AdminChannel.Push("metrics", metrics)
	}

	// This will only compile on Linux due to build tags in resource_monitor files
	resourceMonitor, err := NewResourceMonitor(s.ctx, metricsCallback)
	if err != nil {
		s.logger.Warn("Failed to initialize resource monitor", "error", err)
		// Create a no-op resource monitor to prevent nil pointer dereferences
		// This ensures all ResourceMonitor methods can be called safely
		s.ResourceMonitor = &ResourceMonitor{}
		return
	}
	s.ResourceMonitor = resourceMonitor
	s.logger.Info("Resource monitor initialized")
}
