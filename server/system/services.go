package system

import (
	"context"
	"fmt"
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"syscall"
	"time"

	"github.com/superfly/sprite-env/pkg/container"
	"github.com/superfly/sprite-env/pkg/policy"
	"github.com/superfly/sprite-env/pkg/services"
	"github.com/superfly/sprite-env/pkg/tmux"
)

// initializeServices initializes service components
func (s *System) initializeServices() error {
	// Initialize services manager (for user/process-based services)
	if err := s.initializeServicesManager(); err != nil {
		return fmt.Errorf("failed to initialize services manager: %w", err)
	}

	// Initialize unified service manager (for boot sequence)
	if err := s.initializeUnifiedServiceManager(); err != nil {
		return fmt.Errorf("failed to initialize unified service manager: %w", err)
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

	// Always create services manager (PersistentManager with database)
	servicesManager, err := services.NewManager(servicesDataPath,
		services.WithLogDirForManager(s.config.LogDir))
	if err != nil {
		return err
	}

	s.ServicesManager = servicesManager
	return nil
}

// initializeTMUXManager creates the TMUX manager
func (s *System) initializeTMUXManager() error {
	// Always create a single tmux.Manager instance
	if s.TMUXManager == nil {
		opts := tmux.Options{}
		// Wrap tmux invocations inside the container environment when enabled
		if s.config != nil && s.config.ContainerEnabled {
			opts.WrapCmd = func(c *exec.Cmd) *exec.Cmd {
				return container.Wrap(c, "app", container.WithTTY(false)).Cmd
			}
		}
		s.TMUXManager = tmux.NewManager(s.ctx, opts)
		
		// Bridge tmux activity events to activity monitor
		go s.bridgeTmuxActivityEvents()
	}
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
	resourceMonitor, spriteManager, err := NewResourceMonitor(s.ctx, metricsCallback)
	if err != nil {
		s.logger.Warn("Failed to initialize resource monitor", "error", err)
		// Create a no-op resource monitor to prevent nil pointer dereferences
		// This ensures all ResourceMonitor methods can be called safely
		s.ResourceMonitor = &ResourceMonitor{}
		return
	}
	s.ResourceMonitor = resourceMonitor
	s.SpriteManager = spriteManager
	s.logger.Info("Resource monitor initialized")
}

// initializeUnifiedServiceManager creates the unified service manager for boot sequence
func (s *System) initializeUnifiedServiceManager() error {
	// Create a BaseManager for system services (in-memory only, no database)
	unifiedManager, err := services.NewBaseManager(
		services.WithLogDirBase(s.config.LogDir),
	)
	if err != nil {
		return fmt.Errorf("failed to create unified service manager: %w", err)
	}

	s.UnifiedServiceManager = unifiedManager
	s.logger.Info("Unified service manager created (BaseManager - no database)")
	return nil
}

// registerSystemServices registers all system services with the unified service manager
func (s *System) registerSystemServices() error {
	// Register services in dependency order (though manager handles ordering)

	// Level 0: Independent utilities
	if err := s.UnifiedServiceManager.RegisterService(&services.ServiceDefinition{
		Name:         "reaper",
		Dependencies: []string{},
		Hooks: &services.ServiceHooks{
			Start: func(ctx context.Context, p services.ProgressReporter) error {
				p.ReportProgress("starting zombie reaper")
				s.Reaper.Start()
				p.ReportProgress("zombie reaper started")
				return nil
			},
			Stop: func(ctx context.Context, p services.ProgressReporter) error {
				p.ReportProgress("stopping zombie reaper")
				if err := s.Reaper.Stop(1 * time.Second); err != nil {
					return err
				}
				p.ReportProgress("zombie reaper stopped")
				return nil
			},
		},
	}); err != nil {
		return err
	}

	if err := s.UnifiedServiceManager.RegisterService(&services.ServiceDefinition{
		Name:         "activity_monitor",
		Dependencies: []string{},
		Hooks: &services.ServiceHooks{
			Start: func(ctx context.Context, p services.ProgressReporter) error {
				p.ReportProgress("starting activity monitor")
				s.ActivityMonitor.ActivityStarted("boot")
				s.ActivityMonitor.Start(s.ctx)
				p.ReportProgress("activity monitor started")
				return nil
			},
			Stop: func(ctx context.Context, p services.ProgressReporter) error {
				p.ReportProgress("stopping activity monitor")
				s.ActivityMonitor.Stop()
				p.ReportProgress("activity monitor stopped")
				return nil
			},
		},
	}); err != nil {
		return err
	}

	if err := s.UnifiedServiceManager.RegisterService(&services.ServiceDefinition{
		Name:         "admin_channel",
		Dependencies: []string{},
		Hooks: &services.ServiceHooks{
			Start: func(ctx context.Context, p services.ProgressReporter) error {
				p.ReportProgress("starting admin channel")
				return s.AdminChannel.Start()
			},
			Stop: func(ctx context.Context, p services.ProgressReporter) error {
				p.ReportProgress("stopping admin channel")
				return s.AdminChannel.Stop()
			},
		},
	}); err != nil {
		return err
	}

	if s.config.APIListenAddr != "" {
		if err := s.UnifiedServiceManager.RegisterService(&services.ServiceDefinition{
			Name:         "api_server",
			Dependencies: []string{},
			Hooks: &services.ServiceHooks{
				Start: func(ctx context.Context, p services.ProgressReporter) error {
					p.ReportProgress("starting API server")
					go func() { _ = s.APIServer.Start() }()
					p.ReportProgress("API server started")
					return nil
				},
				Stop: func(ctx context.Context, p services.ProgressReporter) error {
					p.ReportProgress("stopping API server")
					return s.APIServer.Stop(ctx)
				},
			},
		}); err != nil {
			return err
		}
	}

	if err := s.UnifiedServiceManager.RegisterService(&services.ServiceDefinition{
		Name:         "socket_server",
		Dependencies: []string{},
		Hooks: &services.ServiceHooks{
			Start: func(ctx context.Context, p services.ProgressReporter) error {
				p.ReportProgress("starting socket server")
				return s.SocketServer.Start("/tmp/sprite.sock")
			},
			Stop: func(ctx context.Context, p services.ProgressReporter) error {
				p.ReportProgress("stopping socket server")
				return s.SocketServer.Stop()
			},
		},
	}); err != nil {
		return err
	}

	// Level 1: Database manager (no dependencies on other services)
	if err := s.UnifiedServiceManager.RegisterService(&services.ServiceDefinition{
		Name:            "db_manager",
		Dependencies:    []string{},
		MaxHungDuration: 5 * time.Minute, // Litestream restore can take time
		Hooks: &services.ServiceHooks{
			Start: func(ctx context.Context, p services.ProgressReporter) error {
				p.ReportProgress("acquiring database lease")
				return s.DBManager.Start(ctx)
			},
			Stop: func(ctx context.Context, p services.ProgressReporter) error {
				p.ReportProgress("stopping litestream replication")
				return s.DBManager.Stop(ctx)
			},
		},
	}); err != nil {
		return err
	}

	// Level 2: JuiceFS (depends on db_manager for litestream/leaser)
	if s.config.JuiceFSDataPath != "" {
		if err := s.UnifiedServiceManager.RegisterService(&services.ServiceDefinition{
			Name:            "juicefs",
			Dependencies:    []string{"db_manager"},
			MaxHungDuration: 5 * time.Minute, // Mount and cache warmup can take time
			Hooks: &services.ServiceHooks{
				Start: func(ctx context.Context, p services.ProgressReporter) error {
					p.ReportProgress("mounting JuiceFS filesystem")
					return s.JuiceFS.Start(ctx)
				},
				Stop: func(ctx context.Context, p services.ProgressReporter) error {
					p.ReportProgress("flushing JuiceFS cache")
					return s.JuiceFS.Stop(ctx)
				},
			},
		}); err != nil {
			return err
		}
	}

	// Level 3: Overlay (depends on juicefs)
	if s.config.OverlayEnabled {
		deps := []string{}
		if s.config.JuiceFSDataPath != "" {
			deps = append(deps, "juicefs")
		}

		// Determine checkpoint database path
		checkpointDBDir := filepath.Join(s.config.WriteDir, "checkpoints")
		checkpointDBPath := filepath.Join(checkpointDBDir, "checkpoints.db")

		if err := s.UnifiedServiceManager.RegisterService(&services.ServiceDefinition{
			Name:         "overlay",
			Dependencies: deps,
			Hooks: &services.ServiceHooks{
				Start: func(ctx context.Context, p services.ProgressReporter) error {
					p.ReportProgress("initializing overlay manager")
					if err := s.OverlayManager.Start(ctx, checkpointDBPath); err != nil {
						return err
					}
					p.ReportProgress("preparing overlay filesystem")
					s.OverlayManager.UpdateImagePath()
					p.ReportProgress("mounting overlay filesystem")
					if err := s.OverlayManager.PrepareAndMount(ctx); err != nil {
						return err
					}
					p.ReportProgress("mounting checkpoints")
					if err := s.OverlayManager.MountCheckpoints(ctx); err != nil {
						return err
					}
					p.ReportProgress("overlay filesystem ready")
					return nil
				},
				Stop: func(ctx context.Context, p services.ProgressReporter) error {
					p.ReportProgress("unmounting overlay filesystem")
					return s.OverlayManager.Unmount(ctx)
				},
			},
		}); err != nil {
			return err
		}
	}

	// Level 3.5: Network policy manager (after juicefs, before container)
	// Policy manager provides network namespace and veth even when ContainerEnabled=false
	if len(s.config.ProcessCommand) > 0 {
		deps := []string{}
		// Policy depends on JuiceFS so network.json is stored in active/ and checkpointed
		if s.config.JuiceFSDataPath != "" {
			deps = append(deps, "juicefs")
		}

		// Prepare boot config for policy manager
		ifIPv4 := net.ParseIP("10.0.0.2")   // Host side
		peerIPv4 := net.ParseIP("10.0.0.1") // Container side
		ifIPv6 := net.ParseIP("fdf::2")     // Host side
		peerIPv6 := net.ParseIP("fdf::1")   // Container side
		ifName := "spr0-host"
		peerIf := "spr0"
		
		// Store network.json under JuiceFS data/active/policy so it's checkpointed with overlay
		var configDir string
		if s.config.JuiceFSDataPath != "" {
			dataPath := filepath.Join(s.config.JuiceFSDataPath, "data")
			configDir = filepath.Join(dataPath, "active", "policy")
		} else {
			// Fallback to WriteDir if JuiceFS not configured
			configDir = filepath.Join(s.config.WriteDir, "policy")
		}

		var policyMgr *policy.Manager

		if err := s.UnifiedServiceManager.RegisterService(&services.ServiceDefinition{
			Name:         "policy_manager",
			Dependencies: deps,
			Hooks: &services.ServiceHooks{
				Start: func(ctx context.Context, p services.ProgressReporter) error {
					p.ReportProgress("starting policy manager")

					// Ensure policy config directory exists and seed empty config if missing
					if err := os.MkdirAll(configDir, 0755); err != nil {
						return fmt.Errorf("create policy config dir: %w", err)
					}
					cfgPath := filepath.Join(configDir, "network.json")
					if _, err := os.Stat(cfgPath); os.IsNotExist(err) {
						_ = os.WriteFile(cfgPath, []byte("{\n  \"rules\": []\n}\n"), 0644)
					}
					bootCfg := policy.BootConfig{
						ContainerNS:    "sprite",
						OpsNetns:       "",
						IfName:         ifName,
						PeerIfName:     peerIf,
						IfIPv4:         ifIPv4,
						IfIPv6:         ifIPv6,
						PeerIPv4:       peerIPv4,
						PeerIPv6:       peerIPv6,
						IPv4MaskLen:    24,
						IPv6MaskLen:    64,
						DnsPort:        53,
						HostResolvPath: "",
						ConfigDir:      configDir,
						Mode:           policy.Unrestricted,
						ExtraAllow:     nil,
						EnableIPv6:     true,
						TableName:      "sprite_egress",
						SetV4:          "allowed_v4",
						SetV6:          "allowed_v6",
					}
					policyMgr = policy.NewManager(bootCfg)
					return policyMgr.Start(ctx)
				},
				Stop: func(ctx context.Context, p services.ProgressReporter) error {
					p.ReportProgress("stopping policy manager")
					if policyMgr != nil {
						policyMgr.Stop(ctx)
					}
					return nil
				},
			},
		}); err != nil {
			return err
		}
	}

	// Level 4: Container process (depends on overlay and policy_manager)
	if len(s.config.ProcessCommand) > 0 {
		deps := []string{}
		if s.config.OverlayEnabled {
			deps = append(deps, "overlay")
		}
		// Container always depends on policy_manager for network setup
		// Even in unrestricted mode, we need the network namespace and veth pair
		deps = append(deps, "policy_manager")
		if err := s.UnifiedServiceManager.RegisterService(&services.ServiceDefinition{
			Name:         "container",
			Dependencies: deps,
			Hooks: &services.ServiceHooks{
				Start: func(ctx context.Context, p services.ProgressReporter) error {
					p.ReportProgress("starting container process")
					return s.StartProcess()
				},
				Stop: func(ctx context.Context, p services.ProgressReporter) error {
					p.ReportProgress("stopping container process")
					return s.StopProcess()
				},
			},
		}); err != nil {
			return err
		}
	}

	// Level 5: Services manager (depends on container)
	deps := []string{}
	if len(s.config.ProcessCommand) > 0 {
		deps = append(deps, "container")
	}
	if err := s.UnifiedServiceManager.RegisterService(&services.ServiceDefinition{
		Name:         "services_manager",
		Dependencies: deps,
		Hooks: &services.ServiceHooks{
			Start: func(ctx context.Context, p services.ProgressReporter) error {
				p.ReportProgress("starting services manager")
				return s.ServicesManager.Start()
			},
			Stop: func(ctx context.Context, p services.ProgressReporter) error {
				p.ReportProgress("stopping services manager - shutting down user services")
				if err := s.ServicesManager.Stop(ctx); err != nil {
					return err
				}
				syscall.Sync()
				p.ReportProgress("services manager fully stopped")
				return nil
			},
		},
	}); err != nil {
		return err
	}

	s.logger.Info("All system services registered with unified manager")
	return nil
}

// bridgeTmuxActivityEvents bridges tmux active/inactive events to the activity monitor
func (s *System) bridgeTmuxActivityEvents() {
	if s.TMUXManager == nil || s.ActivityMonitor == nil {
		return
	}
	
	eventChan := s.TMUXManager.GetWindowMonitorEvents()
	if eventChan == nil {
		// Window monitor not started yet, wait a bit and retry
		time.Sleep(1 * time.Second)
		eventChan = s.TMUXManager.GetWindowMonitorEvents()
		if eventChan == nil {
			s.logger.Debug("Tmux window monitor not available, skipping activity bridging")
			return
		}
	}
	
	s.logger.Debug("Starting tmux activity event bridge")
	
	for {
		select {
		case <-s.ctx.Done():
			s.logger.Debug("Tmux activity bridge stopped due to context cancellation")
			return
		case event, ok := <-eventChan:
			if !ok {
				s.logger.Debug("Tmux activity bridge stopped due to channel closure")
				return
			}
			
			// Only process active/inactive events
			if event.EventType == "active" {
				source := "tmux:" + event.OriginalSession
				s.ActivityMonitor.ActivityStarted(source)
				s.logger.Debug("Tmux session became active", "session", event.OriginalSession)
			} else if event.EventType == "inactive" {
				source := "tmux:" + event.OriginalSession
				s.ActivityMonitor.ActivityEnded(source)
				s.logger.Debug("Tmux session became inactive", "session", event.OriginalSession)
			}
		}
	}
}
