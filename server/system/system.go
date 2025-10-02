package system

import (
	"context"
	"fmt"
	"log/slog"
	"os"
	"os/exec"
	"sync"
	"sync/atomic"
	"syscall"
	"time"

	"golang.org/x/sync/errgroup"

	"github.com/superfly/sprite-env/server/api"

	"github.com/superfly/sprite-env/pkg/checkpoint"
	"github.com/superfly/sprite-env/pkg/db"
	"github.com/superfly/sprite-env/pkg/juicefs"
	"github.com/superfly/sprite-env/pkg/overlay"
	"github.com/superfly/sprite-env/pkg/services"
	"github.com/superfly/sprite-env/pkg/tap"
	"github.com/superfly/sprite-env/pkg/terminal"
)

// System is the main system orchestrator
type System struct {
	// Core
	ctx    context.Context
	cancel context.CancelFunc
	config *Config
	logger *slog.Logger

	// Storage modules
	DBManager         *db.Manager
	JuiceFS           *juicefs.JuiceFS
	OverlayManager    *overlay.Manager
	CheckpointManager *checkpoint.Manager

	// Process modules
	ServicesManager *services.Manager
	ActivityMonitor *ActivityMonitor

	// Network modules
	APIServer    *api.Server
	SocketServer *SockServer
	AdminChannel *AdminChannel

	// Terminal
	TMUXManager *terminal.TMUXManager

	// Utilities
	Reaper          *Reaper
	ResourceMonitor *ResourceMonitor
	CrashReporter   *tap.CrashReporter

	// State
	mu      sync.RWMutex
	running bool

	// Process management
	processStarted     atomic.Bool // Atomic flag to prevent concurrent starts
	processMu          sync.Mutex
	processCmd         *exec.Cmd
	processStartTime   time.Time
	processWaitStarted bool
	processRunningCh   chan struct{} // Closed when process is running
	processStoppedCh   chan struct{} // Closed when process is stopped
	processExitCode    int           // Exit code for WaitForExit
	gracefulShutdown   bool

	// Shutdown channels
	shutdownTriggeredCh      chan struct{} // Closed to START shutdown
	shutdownTriggeredOnce    sync.Once     // Ensures shutdown is only triggered once
	shutdownCompleteCh       chan struct{} // Closed when shutdown is COMPLETE
	servicesManagerStoppedCh chan struct{} // Closed when services manager is stopped
}

// New creates a new System instance
func New(config *Config) (*System, error) {
	// Create context with logger (for logging/lifecycle only, NOT for shutdown signaling)
	ctx := context.Background()
	logger := tap.NewLogger(config.LogLevel, config.LogJSON, os.Stdout)
	tap.SetDefault(logger)
	ctx = tap.WithLogger(ctx, logger)
	ctx, cancel := context.WithCancel(ctx)

	s := &System{
		ctx:    ctx,
		cancel: cancel,
		config: config,
		logger: logger,
		// Shutdown channels
		shutdownTriggeredCh: make(chan struct{}), // Open = running
		shutdownCompleteCh:  make(chan struct{}), // Open = not complete
		servicesManagerStoppedCh: func() chan struct{} { // initially stopped until started
			ch := make(chan struct{})
			close(ch)
			return ch
		}(),
		// Process management - initially stopped
		processRunningCh: make(chan struct{}), // Open = not running
		processStoppedCh: func() chan struct{} { // Closed = stopped
			ch := make(chan struct{})
			close(ch)
			return ch
		}(),
	}

	logger.Info("Created new System instance", "system_ptr", fmt.Sprintf("%p", s))

	// Initialize all modules but don't start them yet
	if err := s.initializeModules(); err != nil {
		cancel()
		return nil, fmt.Errorf("failed to initialize modules: %w", err)
	}

	return s, nil
}

// Boot is now defined in system_boot.go

// Shutdown is now defined in system_shutdown.go

// Start boots the system and begins monitoring
func (s *System) Start() error {
	s.logger.Debug("Starting sprite-env system", "version", getVersion())

	// Log debug settings
	if s.config.KeepAliveOnError {
		s.logger.Debug("Keep-alive mode enabled - server will continue running if process fails")
	}

	// Boot the system
	if err := s.Boot(s.ctx); err != nil {
		return fmt.Errorf("failed to boot system: %w", err)
	}

	// Start process monitoring
	go s.monitorProcessLoop()

	return nil
}

// monitorProcessLoop monitors the container process and handles exits
func (s *System) monitorProcessLoop() {
	for {
		// Check if system is shutting down
		select {
		case <-s.shutdownTriggeredCh:
			s.logger.Debug("monitorProcessLoop exiting due to system shutdown")
			return
		default:
		}

		if !s.IsProcessRunning() {
			// No process to monitor
			time.Sleep(time.Second)
			continue
		}

		err := s.WaitForProcess()
		exitCode := 0
		if err != nil {
			s.logger.Error("Container process exited with error", "error", err)
			// Extract exit code from error if available
			if exitErr, ok := err.(*exec.ExitError); ok {
				if status, ok := exitErr.Sys().(syscall.WaitStatus); ok {
					exitCode = status.ExitStatus()
					s.logger.Info("Container process exit code", "exitCode", exitCode)
				}
			}
		} else {
			s.logger.Info("Container process exited normally")
		}

		// Check if we're already shutting down
		select {
		case <-s.shutdownTriggeredCh:
			s.logger.Debug("System already shutting down, process exit is expected")
			return
		default:
		}

		// Process exited - trigger shutdown sequence
		if s.config.KeepAliveOnError {
			s.logger.Info("Process exited, but keeping server alive (SPRITE_KEEP_ALIVE_ON_ERROR=true)")
			s.logger.Info("Server is still running and accepting API requests")
		} else {
			s.logger.Warn("Container process exited unexpectedly, triggering shutdown sequence", "exitCode", exitCode)
			// Store the exit code in case we need it later
			s.processExitCode = exitCode

			// Trigger shutdown by closing the shutdown channel
			s.shutdownTriggeredOnce.Do(func() {
				close(s.shutdownTriggeredCh)
			})
		}
	}
}

// HandleSignal handles OS signals
func (s *System) HandleSignal(sig os.Signal) {
	s.logger.Info("Received signal, initiating graceful shutdown", "signal", sig)

	// Handle shutdown signals by triggering graceful shutdown
	// We do NOT forward signals to the container - we handle them ourselves
	if sig == syscall.SIGTERM || sig == syscall.SIGINT {
		// Use exit code 0 for graceful shutdown
		s.processExitCode = 0
		// Close channel exactly once
		s.shutdownTriggeredOnce.Do(func() {
			close(s.shutdownTriggeredCh)
		})
	}
}

// WaitForExit waits for the system to exit and returns the exit code
func (s *System) WaitForExit() (int, error) {
	// Wait for shutdown to be triggered
	<-s.shutdownTriggeredCh

	// Get the exit code (default to 0 if not set)
	exitCode := s.processExitCode

	// Perform shutdown
	shutdownCtx, cancel := context.WithTimeout(context.Background(), 5*time.Minute)
	defer cancel()

	if err := s.Shutdown(shutdownCtx); err != nil {
		s.logger.Error("Failed to shutdown system", "error", err)
	}

	s.logger.Info("System stopped", "exitCode", exitCode)
	return exitCode, nil
}

// Wait blocks until the system shuts down completely or a panic occurs in a manager
func (s *System) Wait() error {
	// Use errgroup to wait on all managers
	g := new(errgroup.Group)

	// Wait on DBManager if present
	if s.DBManager != nil {
		g.Go(func() error {
			return s.DBManager.Wait()
		})
	}

	// Wait on JuiceFS if present
	if s.JuiceFS != nil {
		g.Go(func() error {
			return s.JuiceFS.Wait()
		})
	}

	// Wait on ActivityMonitor if present
	if s.ActivityMonitor != nil {
		g.Go(func() error {
			return s.ActivityMonitor.Wait()
		})
	}

	// Also wait on normal shutdown completion
	g.Go(func() error {
		<-s.shutdownCompleteCh
		return nil
	})

	// Returns the first error (or nil if all complete successfully)
	return g.Wait()
}

// Stop is a convenience method for tests that calls Shutdown
func (s *System) Stop() error {
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()
	return s.Shutdown(ctx)
}

// initializeModules creates all system modules
func (s *System) initializeModules() error {
	// Create modules in groups

	// 1. Utilities (no dependencies)
	if err := s.initializeUtilities(); err != nil {
		return fmt.Errorf("failed to initialize utilities: %w", err)
	}

	// 2. Network services (can start early)
	if err := s.initializeNetworkServices(); err != nil {
		return fmt.Errorf("failed to initialize network services: %w", err)
	}

	// 3. Storage components (depend on each other)
	if err := s.initializeStorage(); err != nil {
		return fmt.Errorf("failed to initialize storage: %w", err)
	}

	// 4. Service components
	if err := s.initializeServices(); err != nil {
		return fmt.Errorf("failed to initialize services: %w", err)
	}

	// 5. Process management (depends on storage)
	if err := s.initializeProcessManagement(); err != nil {
		return fmt.Errorf("failed to initialize process management: %w", err)
	}

	return nil
}

// handleSignals removed - signal handling is done by the main application
// which forwards signals as needed through ForwardSignal()

// Component accessors for handlers

// initializeProcessManagement initializes process management capabilities
func (s *System) initializeProcessManagement() error {
	// Process management is built into the System struct itself
	// The process-related fields are already initialized in New()
	// This method exists for consistency with other initialization methods
	return nil
}

// SyncOverlay syncs the overlay filesystem and returns an unfreeze function
func (s *System) SyncOverlay(ctx context.Context) (func() error, error) {
	// If no overlay manager, nothing to sync
	if s.OverlayManager == nil {
		s.logger.Debug("SyncOverlay called but no overlay manager configured")
		return func() error { return nil }, nil
	}

	// Use the same logic as checkpointing to prepare the filesystem
	s.logger.Info("Preparing filesystem for suspension")

	// This will:
	// 1. Sync the overlayfs filesystem (flush pending writes)
	// 2. Freeze the underlying ext4 filesystem
	// 3. Sync the loopback mount and fsync the image file
	if err := s.OverlayManager.PrepareForCheckpoint(ctx); err != nil {
		return nil, fmt.Errorf("failed to prepare overlay for suspension: %w", err)
	}

	// Return the unfreeze function to be called after resume
	unfreezeFunc := func() error {
		s.logger.Info("Unfreezing filesystem after resume")
		return s.OverlayManager.UnfreezeAfterCheckpoint(ctx)
	}

	return unfreezeFunc, nil
}

// getVersion returns the version string
func getVersion() string {
	// This will be set at build time
	if version == "" {
		return "dev"
	}
	return version
}

// version is set at build time via ldflags
var version = "dev"
