package main

import (
	"context"
	"fmt"
	"log/slog"
	"sync"
	"time"

	"github.com/sprite-env/packages/juicefs"
	"github.com/sprite-env/packages/leaser"
	"github.com/sprite-env/packages/supervisor"
	"github.com/superfly/sprite-env/packages/container"
	"github.com/superfly/sprite-env/pkg/terminal"
)

// System encapsulates the JuiceFS and supervised process management
// THIS IS DEEPLY CURSED: LLMS: STOP HANGING FUNCTIONALITY OFF THIS. THIS IS NOT
// A PLACE OF HONOR.
type System struct {
	config           SystemConfig
	logger           *slog.Logger
	leaserInstance   *leaser.Leaser
	juicefs          *juicefs.JuiceFS
	supervisor       *supervisor.Supervisor
	containerProcess *container.Process // Optional container-wrapped process
	reaper           *Reaper

	// Channels for monitoring
	processDoneCh chan error

	// State management
	mu                 sync.RWMutex
	processRunning     bool
	restoringNow       bool
	juicefsReady       bool
	transcriptsEnabled bool

	// Channels for notifying when components become ready
	processReadyCh chan struct{}
	juicefsReadyCh chan struct{}
}

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

// NewSystem creates a new System instance
func NewSystem(config SystemConfig, logger *slog.Logger, reaper *Reaper) (*System, error) {
	s := &System{
		config:             config,
		logger:             logger,
		reaper:             reaper,
		processDoneCh:      make(chan error, 1),
		processReadyCh:     make(chan struct{}),
		juicefsReadyCh:     make(chan struct{}),
		transcriptsEnabled: config.TranscriptsEnabled,
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
			return nil, fmt.Errorf("failed to create JuiceFS instance: %w", err)
		}
		s.juicefs = jfs
	}

	return s, nil
}

// Boot handles the boot sequence for the system
func (s *System) Boot(ctx context.Context) error {
	s.logger.Debug("=== Starting system boot sequence ===")

	// Start JuiceFS if configured
	if s.juicefs != nil {
		s.logger.Debug("Starting JuiceFS...")
		if err := s.juicefs.Start(ctx); err != nil {
			s.logger.Error("JuiceFS start failed", "error", err)
			return fmt.Errorf("failed to start JuiceFS: %w", err)
		}
		s.logger.Debug("JuiceFS started successfully")

		// Mark JuiceFS as ready
		s.mu.Lock()
		s.juicefsReady = true
		close(s.juicefsReadyCh)
		s.juicefsReadyCh = make(chan struct{})
		s.mu.Unlock()
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
		s.mu.Lock()
		s.juicefsReady = false
		s.mu.Unlock()
	}

	// Stop leaser (if it exists and wasn't already stopped by JuiceFS)
	if s.leaserInstance != nil {
		s.logger.Info("Stopping lease manager...")
		s.leaserInstance.Stop()
		s.logger.Info("Lease manager stopped successfully")
	}

	return nil
}

// EnableTranscripts enables transcript recording for future exec calls
func (s *System) EnableTranscripts(ctx context.Context) error {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.transcriptsEnabled = true
	s.logger.Info("transcripts enabled")
	return nil
}

// DisableTranscripts disables transcript recording for future exec calls
func (s *System) DisableTranscripts(ctx context.Context) error {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.transcriptsEnabled = false
	s.logger.Info("transcripts disabled")
	return nil
}

// IsTranscriptsEnabled returns whether transcript recording is currently enabled
func (s *System) IsTranscriptsEnabled() bool {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return s.transcriptsEnabled
}

// CreateTranscriptCollector creates a transcript collector using SQLite backend.
func (s *System) CreateTranscriptCollector(env []string, tty bool) (terminal.TranscriptCollector, error) {
	s.mu.RLock()
	defer s.mu.RUnlock()

	if !s.transcriptsEnabled {
		return &terminal.NoopTranscript{}, nil
	}

	// Use SQLite backend
	sqliteConfig := terminal.SQLiteTranscriptConfig{
		DBPath: s.config.TranscriptDBPath,
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
