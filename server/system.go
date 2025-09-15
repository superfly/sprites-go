package main

import (
	"context"
	"fmt"
	"log/slog"
	"time"

	"github.com/superfly/sprite-env/pkg/container"
	"github.com/superfly/sprite-env/pkg/juicefs"
	"github.com/superfly/sprite-env/pkg/leaser"
	"github.com/superfly/sprite-env/pkg/supervisor"
	"github.com/superfly/sprite-env/pkg/tap"
)

// SystemConfig holds configuration for the System
type SystemConfig struct {
	// Process configuration
	ProcessCommand                 []string
	ProcessWorkingDir              string
	ProcessEnvironment             []string
	ProcessGracefulShutdownTimeout time.Duration

	// Container configuration
	ContainerEnabled    bool
	ContainerSocketDir  string
	ContainerTTYTimeout time.Duration

	// JuiceFS configuration
	JuiceFSBaseDir    string
	JuiceFSLocalMode  bool
	S3AccessKey       string
	S3SecretAccessKey string
	S3EndpointURL     string
	S3Bucket          string

	// Overlay configuration
	OverlayEnabled       bool
	OverlayImageSize     string
	OverlayLowerPath     string   // Deprecated, use OverlayLowerPaths
	OverlayLowerPaths    []string // Preferred over OverlayLowerPath
	OverlayTargetPath    string
	OverlaySkipOverlayFS bool
}

// systemState holds the mutable state of the system
type systemState struct {
	processRunning bool
	restoringNow   bool
	juicefsReady   bool
}

// stateOp represents state operations
type stateOp struct {
	typ      stateOpType
	field    string
	value    interface{}
	response chan interface{}
}

type stateOpType int

const (
	stateOpGet stateOpType = iota
	stateOpSet
)

// System encapsulates the JuiceFS and supervised process management
type System struct {
	config             SystemConfig
	logger             *slog.Logger
	leaserInstance     *leaser.Leaser
	juicefs            *juicefs.JuiceFS
	supervisor         *supervisor.Supervisor
	containerProcess   *container.Process // Optional container-wrapped process
	reaper             *Reaper
	execProcessTracker interface{} // Will be *execProcessTracker, avoiding import issues
	crashReporter      *tap.CrashReporter
	adminChannel       *AdminChannel

	// Channels for monitoring
	processDoneCh chan error

	// State management via channels
	stateCh  chan stateOp
	stopCh   chan struct{}
	stateMgr *systemState

	// Channels for notifying when components become ready
	processReadyCh chan struct{}
	juicefsReadyCh chan struct{}
}

// NewSystem creates a new System instance
func NewSystem(config SystemConfig, logger *slog.Logger, reaper *Reaper, adminChannel *AdminChannel) (*System, error) {
	s := &System{
		config:         config,
		logger:         logger,
		reaper:         reaper,
		adminChannel:   adminChannel,
		processDoneCh:  make(chan error, 1),
		processReadyCh: make(chan struct{}),
		juicefsReadyCh: make(chan struct{}),
		stateCh:        make(chan stateOp),
		stopCh:         make(chan struct{}),
		stateMgr:       &systemState{},
	}

	// Start state manager goroutine
	go s.runStateManager()

	// Initialize crash reporter
	s3Config := (*tap.S3Config)(nil)
	if config.S3AccessKey != "" && config.S3SecretAccessKey != "" && config.S3EndpointURL != "" && config.S3Bucket != "" {
		s3Config = &tap.S3Config{
			AccessKey:   config.S3AccessKey,
			SecretKey:   config.S3SecretAccessKey,
			EndpointURL: config.S3EndpointURL,
			Bucket:      config.S3Bucket,
		}
	}

	localDir := "/tmp/sprite-env"
	if config.JuiceFSBaseDir != "" {
		localDir = config.JuiceFSBaseDir
	}

	crashReporter, err := tap.NewCrashReporter(logger, localDir, s3Config)
	if err != nil {
		logger.Error("Failed to initialize crash reporter", "error", err)
		// Non-fatal, continue without crash reporting
	} else {
		s.crashReporter = crashReporter
	}

	// Configure container package with system settings
	logger.Info("Configuring container package",
		"enabled", config.ContainerEnabled,
		"socket_dir", config.ContainerSocketDir,
		"tty_timeout", config.ContainerTTYTimeout)

	container.Configure(container.Config{
		Enabled:   config.ContainerEnabled,
		SocketDir: config.ContainerSocketDir,
	})

	if config.ContainerEnabled {
		logger.Info("Container features enabled",
			"socket_dir", config.ContainerSocketDir,
			"tty_timeout", config.ContainerTTYTimeout)
	} else {
		logger.Info("Container features disabled")
	}

	// Set up JuiceFS if base directory is configured
	if config.JuiceFSBaseDir != "" {
		juicefsConfig := juicefs.Config{
			BaseDir:           config.JuiceFSBaseDir,
			LocalMode:         config.JuiceFSLocalMode,
			S3AccessKey:       config.S3AccessKey,
			S3SecretAccessKey: config.S3SecretAccessKey,
			S3EndpointURL:     config.S3EndpointURL,
			S3Bucket:          config.S3Bucket,
			VolumeName:        "sprite-juicefs",
			// Overlay configuration
			OverlayEnabled:       config.OverlayEnabled,
			OverlayImageSize:     config.OverlayImageSize,
			OverlayLowerPath:     config.OverlayLowerPath,
			OverlayLowerPaths:    config.OverlayLowerPaths,
			OverlayTargetPath:    config.OverlayTargetPath,
			OverlaySkipOverlayFS: config.OverlaySkipOverlayFS,
			Logger:               logger,
		}

		// Create leaser for S3 mode (non-local mode)
		if !config.JuiceFSLocalMode && config.S3AccessKey != "" && config.S3SecretAccessKey != "" &&
			config.S3EndpointURL != "" && config.S3Bucket != "" {
			leaserConfig := leaser.Config{
				S3AccessKey:       config.S3AccessKey,
				S3SecretAccessKey: config.S3SecretAccessKey,
				S3EndpointURL:     config.S3EndpointURL,
				S3Bucket:          config.S3Bucket,
				BaseDir:           config.JuiceFSBaseDir,
				Logger:            logger,
			}

			leaserInstance := leaser.New(leaserConfig)
			s.leaserInstance = leaserInstance
			juicefsConfig.LeaseManager = leaserInstance
		}

		jfs, err := juicefs.New(juicefsConfig)
		if err != nil {
			close(s.stopCh)
			return nil, fmt.Errorf("failed to create JuiceFS instance: %w", err)
		}
		s.juicefs = jfs
	}

	return s, nil
}

// runStateManager manages state access via channels
func (s *System) runStateManager() {
	for {
		select {
		case <-s.stopCh:
			return
		case op := <-s.stateCh:
			switch op.typ {
			case stateOpGet:
				var result interface{}
				switch op.field {
				case "processRunning":
					result = s.stateMgr.processRunning
				case "restoringNow":
					result = s.stateMgr.restoringNow
				case "juicefsReady":
					result = s.stateMgr.juicefsReady

				}
				op.response <- result
			case stateOpSet:
				switch op.field {
				case "processRunning":
					s.stateMgr.processRunning = op.value.(bool)
				case "restoringNow":
					s.stateMgr.restoringNow = op.value.(bool)
				case "juicefsReady":
					s.stateMgr.juicefsReady = op.value.(bool)

				}
				close(op.response)
			}
		}
	}
}

// getState retrieves a state field value
func (s *System) getState(field string) interface{} {
	op := stateOp{
		typ:      stateOpGet,
		field:    field,
		response: make(chan interface{}),
	}
	s.stateCh <- op
	return <-op.response
}

// setState updates a state field value
func (s *System) setState(field string, value interface{}) {
	op := stateOp{
		typ:      stateOpSet,
		field:    field,
		value:    value,
		response: make(chan interface{}),
	}
	s.stateCh <- op
	<-op.response
}

// Boot handles the boot sequence for the system
func (s *System) Boot(ctx context.Context) error {
	s.logger.Debug("=== Starting system boot sequence ===")

	// Start JuiceFS if configured
	if s.juicefs != nil {
		s.logger.Debug("Starting JuiceFS...")
		if err := s.juicefs.Start(ctx); err != nil {
			s.logger.Error("JuiceFS start failed", "error", err)

			// Send notification to admin channel
			if s.adminChannel != nil {
				s.adminChannel.SendActivityEvent("juicefs_start_failed", map[string]interface{}{
					"error":     err.Error(),
					"timestamp": time.Now().Unix(),
				})
			}

			return fmt.Errorf("failed to start JuiceFS: %w", err)
		}
		s.logger.Debug("JuiceFS started successfully")

		// Mark JuiceFS as ready
		s.setState("juicefsReady", true)
		close(s.juicefsReadyCh)
		s.juicefsReadyCh = make(chan struct{})
	} else {
		s.logger.Debug("JuiceFS not configured, skipping")
	}

	// Start supervised process if configured
	if len(s.config.ProcessCommand) > 0 {
		s.logger.Info("Starting supervised process...", "command", s.config.ProcessCommand)
		if err := s.StartProcess(); err != nil {
			s.logger.Error("Process start failed", "error", err)
			// If process fails to start, stop JuiceFS
			if s.juicefs != nil {
				s.logger.Info("Stopping JuiceFS due to process start failure")
				stopCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
				defer cancel()
				if stopErr := s.juicefs.Stop(stopCtx); stopErr != nil {
					s.logger.Error("Failed to stop JuiceFS during cleanup", "error", stopErr)
				}
			}
			return fmt.Errorf("failed to start process: %w", err)
		}
		s.logger.Info("Supervised process started successfully")
	} else {
		s.logger.Info("No process command configured, skipping process start")
	}

	s.logger.Debug("=== System boot sequence completed successfully ===")
	return nil
}

// Shutdown performs graceful shutdown of the system
func (s *System) Shutdown(ctx context.Context) error {
	// Stop supervised process
	if err := s.StopProcess(); err != nil {
		s.logger.Error("Failed to stop process during shutdown", "error", err)
	}

	// Stop JuiceFS
	if s.juicefs != nil {
		s.logger.Info("Stopping JuiceFS...")
		if err := s.juicefs.Stop(ctx); err != nil {
			return fmt.Errorf("failed to stop JuiceFS: %w", err)
		}

		// Mark JuiceFS as not ready
		s.setState("juicefsReady", false)
	}

	// Stop leaser (if it exists and wasn't already stopped by JuiceFS)
	if s.leaserInstance != nil {
		s.logger.Info("Stopping lease manager...")
		s.leaserInstance.Stop()
		s.logger.Info("Lease manager stopped successfully")
	}

	// Stop state manager goroutine
	close(s.stopCh)

	return nil
}

// SyncOverlay flushes overlay writes using JuiceFS overlay manager
// Returns a function that must be called to unfreeze the filesystem.
func (s *System) SyncOverlay(ctx context.Context) (func() error, error) {
	if s.juicefs == nil {
		return func() error { return nil }, nil
	}
	return s.juicefs.SyncOverlay(ctx)
}
