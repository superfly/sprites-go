package main

import (
	"context"
	"encoding/json"
	"fmt"
	"log/slog"
	"time"

	"github.com/sprite-env/packages/juicefs"
	"github.com/sprite-env/packages/leaser"
	"github.com/sprite-env/packages/supervisor"
	"github.com/superfly/sprite-env/packages/container"
	portwatcher "github.com/superfly/sprite-env/packages/port-watcher"
	"github.com/superfly/sprite-env/pkg/terminal"
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
	OverlayLowerPath     string
	OverlayTargetPath    string
	OverlaySkipOverlayFS bool

	// Transcripts configuration
	TranscriptsEnabled bool
	TranscriptDBPath   string
}

// systemState holds the mutable state of the system
type systemState struct {
	processRunning     bool
	restoringNow       bool
	juicefsReady       bool
	configured         bool
	dynamicConfigPath  string
	transcriptsEnabled bool
	transcriptDBPath   string
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
	portWatcher        *portwatcher.PortWatcher
	portTracker        interface{} // Will be *portTracker, but avoiding circular import
	execProcessTracker interface{} // Will be *execProcessTracker, avoiding import issues

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
func NewSystem(config SystemConfig, logger *slog.Logger, reaper *Reaper) (*System, error) {
	return NewSystemWithDynamicConfig(config, "", logger, reaper)
}

// NewSystemWithDynamicConfig creates a new System instance with dynamic config support
func NewSystemWithDynamicConfig(config SystemConfig, dynamicConfigPath string, logger *slog.Logger, reaper *Reaper) (*System, error) {
	s := &System{
		config:         config,
		logger:         logger,
		reaper:         reaper,
		processDoneCh:  make(chan error, 1),
		processReadyCh: make(chan struct{}),
		juicefsReadyCh: make(chan struct{}),
		stateCh:        make(chan stateOp),
		stopCh:         make(chan struct{}),
		stateMgr: &systemState{
			configured:         false,
			dynamicConfigPath:  dynamicConfigPath,
			transcriptsEnabled: config.TranscriptsEnabled,
			transcriptDBPath:   config.TranscriptDBPath,
		},
	}

	// Start state manager goroutine
	go s.runStateManager()

	// For backward compatibility, if config is already populated, configure immediately
	if config.JuiceFSBaseDir != "" || config.ContainerEnabled || len(config.ProcessCommand) > 0 {
		if err := s.Configure(config); err != nil {
			close(s.stopCh)
			return nil, err
		}
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
				case "configured":
					result = s.stateMgr.configured
				case "dynamicConfigPath":
					result = s.stateMgr.dynamicConfigPath
				case "processRunning":
					result = s.stateMgr.processRunning
				case "restoringNow":
					result = s.stateMgr.restoringNow
				case "juicefsReady":
					result = s.stateMgr.juicefsReady
				case "transcriptsEnabled":
					result = s.stateMgr.transcriptsEnabled
				case "transcriptDBPath":
					result = s.stateMgr.transcriptDBPath
				}
				op.response <- result
			case stateOpSet:
				switch op.field {
				case "configured":
					s.stateMgr.configured = op.value.(bool)
				case "processRunning":
					s.stateMgr.processRunning = op.value.(bool)
				case "restoringNow":
					s.stateMgr.restoringNow = op.value.(bool)
				case "juicefsReady":
					s.stateMgr.juicefsReady = op.value.(bool)
				case "transcriptsEnabled":
					s.stateMgr.transcriptsEnabled = op.value.(bool)
				case "transcriptDBPath":
					s.stateMgr.transcriptDBPath = op.value.(string)
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

// Configure sets up the system with the provided configuration
func (s *System) Configure(config interface{}) error {
	if s.getState("configured").(bool) {
		return fmt.Errorf("system already configured")
	}

	var sysConfig SystemConfig

	// Try direct type assertion first
	if sc, ok := config.(SystemConfig); ok {
		sysConfig = sc
	} else {
		// If not SystemConfig, try JSON conversion
		// This allows handlers to pass their own config struct
		jsonData, err := json.Marshal(config)
		if err != nil {
			return fmt.Errorf("failed to marshal config: %w", err)
		}

		if err := json.Unmarshal(jsonData, &sysConfig); err != nil {
			return fmt.Errorf("failed to unmarshal config to SystemConfig: %w", err)
		}
	}

	s.config = sysConfig

	// Configure container package with system settings
	s.logger.Info("Configuring container package",
		"enabled", sysConfig.ContainerEnabled,
		"socket_dir", sysConfig.ContainerSocketDir,
		"tty_timeout", sysConfig.ContainerTTYTimeout)

	container.Configure(container.Config{
		Enabled:   sysConfig.ContainerEnabled,
		SocketDir: sysConfig.ContainerSocketDir,
	})

	if sysConfig.ContainerEnabled {
		s.logger.Info("Container features enabled",
			"socket_dir", sysConfig.ContainerSocketDir,
			"tty_timeout", sysConfig.ContainerTTYTimeout)
	} else {
		s.logger.Info("Container features disabled")
	}

	// Set up JuiceFS if base directory is configured
	if sysConfig.JuiceFSBaseDir != "" {
		juicefsConfig := juicefs.Config{
			BaseDir:           sysConfig.JuiceFSBaseDir,
			LocalMode:         sysConfig.JuiceFSLocalMode,
			S3AccessKey:       sysConfig.S3AccessKey,
			S3SecretAccessKey: sysConfig.S3SecretAccessKey,
			S3EndpointURL:     sysConfig.S3EndpointURL,
			S3Bucket:          sysConfig.S3Bucket,
			VolumeName:        "sprite-juicefs",
			// Overlay configuration
			OverlayEnabled:       sysConfig.OverlayEnabled,
			OverlayImageSize:     sysConfig.OverlayImageSize,
			OverlayLowerPath:     sysConfig.OverlayLowerPath,
			OverlayTargetPath:    sysConfig.OverlayTargetPath,
			OverlaySkipOverlayFS: sysConfig.OverlaySkipOverlayFS,
			Logger:               s.logger,
		}

		// Create leaser for S3 mode (non-local mode)
		if !sysConfig.JuiceFSLocalMode && sysConfig.S3AccessKey != "" && sysConfig.S3SecretAccessKey != "" &&
			sysConfig.S3EndpointURL != "" && sysConfig.S3Bucket != "" {
			leaserConfig := leaser.Config{
				S3AccessKey:       sysConfig.S3AccessKey,
				S3SecretAccessKey: sysConfig.S3SecretAccessKey,
				S3EndpointURL:     sysConfig.S3EndpointURL,
				S3Bucket:          sysConfig.S3Bucket,
				BaseDir:           sysConfig.JuiceFSBaseDir,
				Logger:            s.logger,
			}

			leaserInstance := leaser.New(leaserConfig)
			s.leaserInstance = leaserInstance
			juicefsConfig.LeaseManager = leaserInstance
		}

		jfs, err := juicefs.New(juicefsConfig)
		if err != nil {
			return fmt.Errorf("failed to create JuiceFS instance: %w", err)
		}
		s.juicefs = jfs
	}

	s.setState("configured", true)
	return nil
}

// IsConfigured returns whether the system has been configured
func (s *System) IsConfigured() bool {
	return s.getState("configured").(bool)
}

// GetDynamicConfigPath returns the dynamic config path if set
func (s *System) GetDynamicConfigPath() string {
	return s.getState("dynamicConfigPath").(string)
}

// Boot handles the boot sequence for the system
func (s *System) Boot(ctx context.Context) error {
	s.logger.Debug("=== Starting system boot sequence ===")

	if !s.IsConfigured() {
		return fmt.Errorf("system not configured, cannot boot")
	}

	// Start JuiceFS if configured
	if s.juicefs != nil {
		s.logger.Debug("Starting JuiceFS...")
		if err := s.juicefs.Start(ctx); err != nil {
			s.logger.Error("JuiceFS start failed", "error", err)
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

// SetTranscriptDBPath sets the path for the transcript database
func (s *System) SetTranscriptDBPath(path string) {
	s.setState("transcriptDBPath", path)
}

// EnableTranscripts enables transcript recording for future exec calls
func (s *System) EnableTranscripts(ctx context.Context) error {
	s.setState("transcriptsEnabled", true)
	s.logger.Info("transcripts enabled")
	return nil
}

// DisableTranscripts disables transcript recording for future exec calls
func (s *System) DisableTranscripts(ctx context.Context) error {
	s.setState("transcriptsEnabled", false)
	s.logger.Info("transcripts disabled")
	return nil
}

// IsTranscriptsEnabled returns whether transcript recording is currently enabled
func (s *System) IsTranscriptsEnabled() bool {
	return s.getState("transcriptsEnabled").(bool)
}

// CreateTranscriptCollector creates a transcript collector using SQLite backend.
func (s *System) CreateTranscriptCollector(env []string, tty bool) (terminal.TranscriptCollector, error) {
	if !s.IsTranscriptsEnabled() {
		return &terminal.NoopTranscript{}, nil
	}

	// Use SQLite backend
	dbPath := s.getState("transcriptDBPath").(string)
	if dbPath == "" {
		dbPath = s.config.TranscriptDBPath
	}

	sqliteConfig := terminal.SQLiteTranscriptConfig{
		DBPath: dbPath,
		Env:    env,
		TTY:    tty,
		Logger: s.logger,
	}

	sqliteTranscript, err := terminal.NewSQLiteTranscript(sqliteConfig)
	if err != nil {
		return nil, fmt.Errorf("failed to create SQLite transcript: %w", err)
	}

	s.logger.Debug("Created SQLite transcript", "sessionID", sqliteTranscript.GetSessionID())
	return sqliteTranscript, nil
}
