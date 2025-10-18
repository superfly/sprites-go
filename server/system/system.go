package system

import (
	"context"
	"errors"
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

	"github.com/superfly/sprite-env/pkg/container"
	"github.com/superfly/sprite-env/pkg/db"
	"github.com/superfly/sprite-env/pkg/juicefs"
	"github.com/superfly/sprite-env/pkg/overlay"
	"github.com/superfly/sprite-env/pkg/services"
	"github.com/superfly/sprite-env/pkg/tap"
	"github.com/superfly/sprite-env/pkg/tmux"
)

// System is the main system orchestrator
type System struct {
	// Core
	ctx         context.Context
	cancel      context.CancelFunc
	config      *Config
	logger      *slog.Logger
	Environment Environment

	// Storage modules
	DBManager      *db.Manager
	JuiceFS        *juicefs.JuiceFS
	OverlayManager *overlay.Manager

	// Process modules
	ServicesManager *services.Manager
	ActivityMonitor *ActivityMonitor

	// Network modules
	APIServer    *api.Server
	SocketServer *SockServer
	AdminChannel *AdminChannel

	// Terminal
	TMUXManager *tmux.Manager

	// Utilities
	Reaper          *Reaper
	ResourceMonitor *ResourceMonitor
	CrashReporter   *tap.CrashReporter

	// State
	mu      sync.RWMutex
	running bool

	// Process management
	processStarted      atomic.Bool // Atomic flag to prevent concurrent starts
	processMu           sync.Mutex
	processCmd          *exec.Cmd
	processStartTime    time.Time
	processWaitStarted  bool
	processStartedCh    chan struct{} // Closed when process is running
	processStoppedCh    chan struct{} // Closed when process is stopped
	processExitCode     atomic.Int32  // Exit code for WaitForExit
	processExitCodeSet  atomic.Bool   // Track if exit code has been set
	gracefulShutdown    bool
	restoringInProgress atomic.Bool // Flag to prevent shutdown trigger during restore
	userEnvMaintenance  atomic.Bool // Flag to prevent global shutdown during container-only ops

	// Shutdown channels
	shutdownTriggeredCh      chan struct{} // Closed to START shutdown
	shutdownTriggeredOnce    sync.Once     // Ensures shutdown is only triggered once
	shutdownCompleteCh       chan struct{} // Closed when shutdown is COMPLETE
	servicesManagerStoppedCh chan struct{} // Closed when services manager is stopped

	// Boot coordination
	// bootDoneCh is open while Boot() is in progress and closed when Boot() returns
	// This allows Shutdown() to block until the current boot step completes
	bootDoneCh chan struct{}
}

// ErrShutdownDuringBoot is returned by Boot when shutdown is triggered mid-boot.
var ErrShutdownDuringBoot = errors.New("shutdown triggered during boot")

// New creates a new System instance
func New(config *Config) (*System, error) {
	// Create context with logger (for logging/lifecycle only, NOT for shutdown signaling)
	ctx := context.Background()
	logger := tap.NewLogger(config.LogLevel, config.LogJSON, os.Stdout)
	tap.SetDefault(logger)
	ctx = tap.WithLogger(ctx, logger)
	ctx, cancel := context.WithCancel(ctx)

	// Choose environment implementation based on Fly env vars
	var env Environment
	if os.Getenv("FLY_APP_NAME") != "" && os.Getenv("FLY_MACHINE_ID") != "" {
		env = NewFlyEnvironment()
	} else {
		env = NewLocalEnvironment()
	}

	s := &System{
		ctx:         ctx,
		cancel:      cancel,
		config:      config,
		logger:      logger,
		Environment: env,
		// Shutdown channels
		shutdownTriggeredCh: make(chan struct{}), // Open = running
		shutdownCompleteCh:  make(chan struct{}), // Open = not complete
		servicesManagerStoppedCh: func() chan struct{} { // initially stopped until started
			ch := make(chan struct{})
			close(ch)
			return ch
		}(),
		// Process management - initially stopped
		processStartedCh: make(chan struct{}), // Open = not running
		processStoppedCh: func() chan struct{} { // Closed = stopped
			ch := make(chan struct{})
			close(ch)
			return ch
		}(),
		// Boot coordination - not booting initially (closed channel)
		bootDoneCh: func() chan struct{} {
			ch := make(chan struct{})
			close(ch)
			return ch
		}(),
	}

	// Default exit code to -1 to detect race conditions where it's read before being set
	s.processExitCode.Store(-1)
	s.processExitCodeSet.Store(false) // Not yet set by actual process

	logger.Info("Created new System instance", "system_ptr", fmt.Sprintf("%p", s))

	// Initialize all modules but don't start them yet
	if err := s.initializeModules(); err != nil {
		cancel()
		return nil, fmt.Errorf("failed to initialize modules: %w", err)
	}

	// Register callback for sprite info changes
	RegisterSpriteInfoChangeCallback(func(info *SpriteInfo) {
		s.handleSpriteInfoChange(info)
	})

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
	// Re-open bootDoneCh to indicate boot in progress
	s.bootDoneCh = make(chan struct{})
	if err := s.Boot(s.ctx); err != nil {
		if errors.Is(err, ErrShutdownDuringBoot) {
			s.logger.Info("Boot aborted due to shutdown; treating as successful shutdown initiation")
			return nil
		}
		return fmt.Errorf("failed to boot system: %w", err)
	}

	// Start process monitoring
	go s.monitorProcessLoop()

	return nil
}

// GetProcessExitCode returns the process exit code as an int
func (s *System) GetProcessExitCode() int {
	return int(s.processExitCode.Load())
}

// SetProcessExitCode sets the process exit code and warns if called multiple times
func (s *System) SetProcessExitCode(exitCode int, source string) {
	if s.processExitCodeSet.Swap(true) {
		// Exit code was already set
		oldValue := s.processExitCode.Load()
		s.logger.Warn("Process exit code being overwritten",
			"oldValue", oldValue,
			"newValue", exitCode,
			"source", source)
	}
	s.processExitCode.Store(int32(exitCode))
	s.logger.Info("Process exit code set", "exitCode", exitCode, "source", source)
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

		// Wait for process to exit
		// Note: monitorProcess() has already stored the exit code in s.processExitCode
		err := s.WaitForProcess()
		if err != nil {
			s.logger.Error("Error waiting for process", "error", err)
		}

		// Get the exit code that was stored by monitorProcess()
		exitCode := s.GetProcessExitCode()

		s.logger.Info("Container process exited with code", "exitCode", exitCode)

		// Check if we're already shutting down
		select {
		case <-s.shutdownTriggeredCh:
			s.logger.Debug("System already shutting down, process exit is expected")
			return
		default:
		}

		// Check if we're in the middle of a restore operation
		if s.restoringInProgress.Load() {
			s.logger.Debug("Process exit during restore operation, not triggering shutdown")
			// Poll every 200ms for up to 1 second waiting for restore to complete
			for i := 0; i < 5; i++ {
				time.Sleep(200 * time.Millisecond)
				if !s.restoringInProgress.Load() {
					s.logger.Debug("Restore completed, resuming process monitoring")
					break
				}
			}
			continue
		}

		// Process exited - trigger shutdown sequence unless in user-env maintenance
		if s.userEnvMaintenance.Load() {
			s.logger.Info("Process exited during user-environment maintenance; not triggering full system shutdown")
			return
		}
		if s.config.KeepAliveOnError {
			s.logger.Info("Process exited, but keeping server alive (SPRITE_KEEP_ALIVE_ON_ERROR=true)")
			s.logger.Info("Server is still running and accepting API requests")
		} else {
			s.logger.Warn("Container process exited unexpectedly, triggering shutdown sequence", "exitCode", exitCode)
			// Exit code already stored by monitorProcess(), just trigger shutdown

			// Trigger shutdown by closing the shutdown channel
			s.shutdownTriggeredOnce.Do(func() {
				close(s.shutdownTriggeredCh)
			})
		}
	}
}

// HandleSignal handles OS signals
//
// Signal handling philosophy:
// - When we receive a shutdown signal (SIGTERM/SIGINT), we forward it to the supervised process
// - We mark this as an expected/graceful shutdown so we don't generate crash reports
// - We let the process exit naturally with its own exit code
// - monitorProcessLoop will detect the exit and trigger system shutdown
// - The process's actual exit code is preserved and used as the system exit code
//
// We do NOT set the exit code to 0 ourselves - the process decides its exit code.
// We do NOT directly trigger shutdown here - we let the natural flow happen:
//
//	Signal → Forward to process → Process exits → monitorProcessLoop triggers shutdown
func (s *System) HandleSignal(sig os.Signal) {
	s.logger.Info("Received signal, forwarding to process", "signal", sig)

	if sig == syscall.SIGTERM || sig == syscall.SIGINT {
		// Mark this as a graceful shutdown to avoid crash reporting
		s.processMu.Lock()
		s.gracefulShutdown = true
		s.processMu.Unlock()

		// Forward the signal to the supervised process
		// The process will exit, monitorProcessLoop will detect it, and trigger shutdown
		if err := s.ForwardSignal(sig); err != nil {
			s.logger.Error("Failed to forward signal to process", "signal", sig, "error", err)
			// If we can't forward the signal (e.g., process already stopped),
			// trigger shutdown directly
			s.shutdownTriggeredOnce.Do(func() {
				close(s.shutdownTriggeredCh)
			})
		}
	}
}

// WaitForExit waits for the system to exit and returns the exit code
func (s *System) WaitForExit() (int, error) {
	// Wait for shutdown to be triggered
	<-s.shutdownTriggeredCh

	// Get the exit code
	exitCode := s.GetProcessExitCode()

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

// Logger returns the system's logger
func (s *System) Logger() *slog.Logger {
	return s.logger
}

// WithLogger sets a new logger for the system
// This is useful for adding context attributes in tests
func (s *System) WithLogger(logger *slog.Logger) {
	s.logger = logger
	// Update context with new logger
	s.ctx = tap.WithLogger(s.ctx, logger)
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

// WrapContainer wraps the command for container execution if ContainerEnabled.
// If not enabled, returns the original command.
func (s *System) WrapContainer(cmd *exec.Cmd, tty bool) *exec.Cmd {
	if !s.config.ContainerEnabled {
		return cmd
	}
	wrapped := container.Wrap(cmd, "app", container.WithTTY(tty))
	return wrapped.Cmd
}

// GetTMUXManager returns the tmux manager instance
func (s *System) GetTMUXManager() *tmux.Manager {
	return s.TMUXManager
}

// GetOverlayManager returns the overlay manager (may be nil)
func (s *System) GetOverlayManager() *overlay.Manager {
	return s.OverlayManager
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
