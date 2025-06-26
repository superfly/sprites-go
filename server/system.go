package main

import (
	"context"
	"fmt"
	"log/slog"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"time"

	"github.com/sprite-env/lib/api"

	"github.com/sprite-env/packages/juicefs"
	"github.com/sprite-env/packages/leaser"
	"github.com/sprite-env/packages/supervisor"
	"github.com/superfly/sprite-env/packages/container"
)

// System encapsulates the JuiceFS and supervised process management
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
	mu             sync.RWMutex
	processRunning bool
	restoringNow   bool
	juicefsReady   bool

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
}

// NewSystem creates a new System instance
func NewSystem(config SystemConfig, logger *slog.Logger, reaper *Reaper) (*System, error) {
	s := &System{
		config:         config,
		logger:         logger,
		reaper:         reaper,
		processDoneCh:  make(chan error, 1),
		processReadyCh: make(chan struct{}),
		juicefsReadyCh: make(chan struct{}),
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
		if config.S3AccessKey != "" && config.S3SecretAccessKey != "" &&
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
	s.logger.Info("=== Starting system boot sequence ===")

	// Start JuiceFS if configured
	if s.juicefs != nil {
		s.logger.Info("Starting JuiceFS...")
		if err := s.juicefs.Start(ctx); err != nil {
			s.logger.Error("JuiceFS start failed", "error", err)
			return fmt.Errorf("failed to start JuiceFS: %w", err)
		}
		s.logger.Info("JuiceFS started successfully")

		// Mark JuiceFS as ready
		s.mu.Lock()
		s.juicefsReady = true
		close(s.juicefsReadyCh)
		s.juicefsReadyCh = make(chan struct{})
		s.mu.Unlock()
	} else {
		s.logger.Info("JuiceFS not configured, skipping")
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

	s.logger.Info("=== System boot sequence completed successfully ===")
	return nil
}

// StartProcess starts the supervised process
func (s *System) StartProcess() error {
	s.mu.Lock()
	defer s.mu.Unlock()

	s.logger.Info("StartProcess: Entering method")

	if len(s.config.ProcessCommand) == 0 {
		s.logger.Error("StartProcess: No process command configured")
		return fmt.Errorf("no process command configured")
	}

	s.logger.Info("StartProcess: Setting up working directory", "command", s.config.ProcessCommand)

	// Set up process working directory
	workingDir := s.config.ProcessWorkingDir
	if s.juicefs != nil && workingDir == "" {
		// Default to JuiceFS active directory if available
		workingDir = filepath.Join(s.config.JuiceFSBaseDir, "data", "active", "fs")
		s.logger.Info("StartProcess: Using JuiceFS default working directory", "workingDir", workingDir)
	}

	s.logger.Info("StartProcess: Final working directory", "workingDir", workingDir)

	// Check if working directory exists
	if workingDir != "" {
		if stat, err := os.Stat(workingDir); err != nil {
			s.logger.Error("StartProcess: Working directory does not exist", "workingDir", workingDir, "error", err)
			return fmt.Errorf("working directory does not exist: %s: %w", workingDir, err)
		} else {
			s.logger.Info("StartProcess: Working directory exists", "workingDir", workingDir, "isDir", stat.IsDir())
		}
	}

	supervisorConfig := supervisor.Config{
		Command:     s.config.ProcessCommand[0],
		Args:        s.config.ProcessCommand[1:],
		GracePeriod: s.config.ProcessGracefulShutdownTimeout,
		Env:         append(os.Environ(), s.config.ProcessEnvironment...),
		Dir:         workingDir,
		Logger:      s.logger,
	}

	s.logger.Info("StartProcess: Creating supervisor",
		"command", supervisorConfig.Command,
		"args", supervisorConfig.Args,
		"gracePeriod", supervisorConfig.GracePeriod,
		"dir", supervisorConfig.Dir,
		"envCount", len(supervisorConfig.Env))

	// Validate that the command exists and is executable
	if _, err := exec.LookPath(supervisorConfig.Command); err != nil {
		s.logger.Error("StartProcess: Command not found in PATH", "command", supervisorConfig.Command, "error", err)
		return fmt.Errorf("command not found: %s: %w", supervisorConfig.Command, err)
	}

	// Check if it's an absolute path that exists
	if filepath.IsAbs(supervisorConfig.Command) {
		if stat, err := os.Stat(supervisorConfig.Command); err != nil {
			s.logger.Error("StartProcess: Command file does not exist", "command", supervisorConfig.Command, "error", err)
			return fmt.Errorf("command file does not exist: %s: %w", supervisorConfig.Command, err)
		} else if stat.Mode()&0111 == 0 {
			s.logger.Error("StartProcess: Command file is not executable", "command", supervisorConfig.Command)
			return fmt.Errorf("command file is not executable: %s", supervisorConfig.Command)
		}
	}

	s.logger.Info("StartProcess: Command validation successful")

	// Use container-wrapped process if containers are enabled, otherwise use basic supervisor
	if s.config.ContainerEnabled {
		s.logger.Info("StartProcess: Creating container-wrapped process")

		processConfig := container.ProcessConfig{
			Config: supervisor.Config{
				Command:     s.config.ProcessCommand[0],
				Args:        s.config.ProcessCommand[1:],
				GracePeriod: s.config.ProcessGracefulShutdownTimeout,
				Env:         append(os.Environ(), s.config.ProcessEnvironment...),
				Dir:         workingDir,
				Logger:      s.logger,
			},
			TTYTimeout: s.config.ContainerTTYTimeout,
			TTYOutput:  os.Stdout, // Forward TTY output to logs
		}

		containerProcess, err := container.NewProcess(processConfig)
		if err != nil {
			s.logger.Error("StartProcess: Failed to create container process", "error", err)
			return fmt.Errorf("failed to create container process: %w", err)
		}

		s.logger.Info("StartProcess: Container process created successfully, starting process")

		pid, err := containerProcess.Start()
		if err != nil {
			s.logger.Error("StartProcess: Failed to start container process", "error", err)
			return fmt.Errorf("failed to start container process: %w", err)
		}

		// Store the container process (which embeds the supervisor)
		s.supervisor = containerProcess.Supervisor
		s.containerProcess = containerProcess
		s.processRunning = true

		s.logger.Info("StartProcess: Container process started successfully", "pid", pid, "command", s.config.ProcessCommand)

	} else {
		s.logger.Info("StartProcess: Creating basic supervisor (containers disabled)")

		sup, err := supervisor.New(supervisorConfig)
		if err != nil {
			s.logger.Error("StartProcess: Failed to create supervisor", "error", err)
			return fmt.Errorf("failed to create supervisor: %w", err)
		}

		s.logger.Info("StartProcess: Supervisor created successfully, starting process")

		pid, err := sup.Start()
		if err != nil {
			s.logger.Error("StartProcess: Failed to start process", "error", err)
			return fmt.Errorf("failed to start process: %w", err)
		}

		s.supervisor = sup
		s.processRunning = true

		s.logger.Info("StartProcess: Process started successfully", "pid", pid, "command", s.config.ProcessCommand)
	}

	// Close the old channel and create a new one for future waits
	close(s.processReadyCh)
	s.processReadyCh = make(chan struct{})

	// Monitor process in background
	go func() {
		s.logger.Info("StartProcess: Starting background process monitor")
		err := s.supervisor.Wait()
		s.logger.Info("StartProcess: Process monitor detected process exit", "error", err)
		s.processDoneCh <- err

		s.mu.Lock()
		s.processRunning = false
		s.mu.Unlock()
		s.logger.Info("StartProcess: Background monitor completed")
	}()

	s.logger.Info("StartProcess: Method completed successfully")
	return nil
}

// StopProcess stops the supervised process
func (s *System) StopProcess() error {
	s.mu.Lock()
	defer s.mu.Unlock()

	if !s.processRunning || s.supervisor == nil {
		return nil
	}

	s.logger.Info("Stopping supervised process...")

	// Stop container process if available, otherwise stop basic supervisor
	if s.containerProcess != nil {
		if err := s.containerProcess.Stop(); err != nil {
			return fmt.Errorf("failed to stop container process: %w", err)
		}
		s.containerProcess = nil
	} else {
		if err := s.supervisor.Stop(); err != nil {
			return fmt.Errorf("failed to stop process: %w", err)
		}
	}

	s.processRunning = false
	s.logger.Info("Process stopped successfully")
	return nil
}

// Wait waits for the supervised process to complete
func (s *System) Wait() error {
	// If no process is running, return immediately
	s.mu.RLock()
	if !s.processRunning {
		s.mu.RUnlock()
		return nil
	}
	s.mu.RUnlock()

	// Wait for process to complete
	err := <-s.processDoneCh
	return err
}

// IsProcessRunning returns whether the supervised process is running
func (s *System) IsProcessRunning() bool {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return s.processRunning
}

// WaitForProcessRunning blocks until the process is running
// Returns immediately if already running
func (s *System) WaitForProcessRunning(ctx context.Context) error {
	s.mu.RLock()
	if s.processRunning {
		s.mu.RUnlock()
		return nil
	}
	ch := s.processReadyCh
	s.mu.RUnlock()

	// Wait for process to be ready or context to be cancelled
	select {
	case <-ch:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	}
}

// IsJuiceFSReady returns whether JuiceFS is ready
func (s *System) IsJuiceFSReady() bool {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return s.juicefsReady
}

// WaitForJuiceFS blocks until JuiceFS is ready
// Returns immediately if already ready or not configured
func (s *System) WaitForJuiceFS(ctx context.Context) error {
	s.mu.RLock()
	// If JuiceFS is not configured, it's "ready" (nothing to wait for)
	if s.juicefs == nil {
		s.mu.RUnlock()
		return nil
	}
	if s.juicefsReady {
		s.mu.RUnlock()
		return nil
	}
	ch := s.juicefsReadyCh
	s.mu.RUnlock()

	// Wait for JuiceFS to be ready or context to be cancelled
	select {
	case <-ch:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	}
}

// IsRestoring returns whether the system is currently restoring
func (s *System) IsRestoring() bool {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return s.restoringNow
}

// Checkpoint creates a checkpoint of the current system state
func (s *System) Checkpoint(ctx context.Context, checkpointID string) error {
	if s.juicefs == nil {
		return fmt.Errorf("JuiceFS not configured")
	}

	// Use the proper JuiceFS checkpoint method that handles overlay
	// Note: checkpointID parameter is ignored, version is auto-generated
	if err := s.juicefs.Checkpoint(ctx, ""); err != nil {
		return fmt.Errorf("failed to create checkpoint: %w", err)
	}

	s.logger.Info("Checkpoint created successfully")
	return nil
}

// CheckpointAndGetVersion creates a checkpoint and returns the version used
func (s *System) CheckpointAndGetVersion(ctx context.Context) (string, error) {
	if s.juicefs == nil {
		return "", fmt.Errorf("JuiceFS not configured")
	}

	version, err := s.juicefs.CheckpointWithVersion(ctx)
	if err != nil {
		return "", fmt.Errorf("failed to create checkpoint: %w", err)
	}

	s.logger.Info("Checkpoint created successfully", "version", version)
	return version, nil
}

// Restore restores the system from a checkpoint
func (s *System) Restore(ctx context.Context, checkpointID string) error {
	s.mu.Lock()
	s.restoringNow = true
	s.mu.Unlock()

	defer func() {
		s.mu.Lock()
		s.restoringNow = false
		s.mu.Unlock()
	}()

	if checkpointID == "" {
		return fmt.Errorf("checkpoint ID is required")
	}

	if s.juicefs == nil {
		return fmt.Errorf("JuiceFS not configured")
	}

	s.logger.Info("Starting restore sequence", "checkpointID", checkpointID)

	// Stop process if running
	if err := s.StopProcess(); err != nil {
		return fmt.Errorf("failed to stop process for restore: %w", err)
	}

	// Perform JuiceFS restore
	s.logger.Info("Restoring from checkpoint", "checkpointID", checkpointID)
	if err := s.juicefs.Restore(ctx, checkpointID); err != nil {
		return fmt.Errorf("failed to restore checkpoint: %w", err)
	}

	// Restart process
	s.logger.Info("Starting process after restore")
	if err := s.StartProcess(); err != nil {
		return fmt.Errorf("failed to start process after restore: %w", err)
	}

	s.logger.Info("Restore sequence completed")
	return nil
}

// CheckpointWithStream creates a checkpoint with streaming output
func (s *System) CheckpointWithStream(ctx context.Context, checkpointID string, streamCh chan<- api.StreamMessage) error {
	defer close(streamCh)

	if s.juicefs == nil {
		return fmt.Errorf("JuiceFS not configured")
	}

	// Send initial message
	streamCh <- api.StreamMessage{
		Type: "info",
		Data: "Creating checkpoint...",
		Time: time.Now(),
	}

	// Use the proper JuiceFS checkpoint method that handles overlay
	// Get the version that will be used
	version, err := s.juicefs.CheckpointWithVersion(ctx)
	if err != nil {
		streamCh <- api.StreamMessage{
			Type:  "error",
			Error: fmt.Sprintf("Failed to create checkpoint: %v", err),
			Time:  time.Now(),
		}
		return err
	}

	streamCh <- api.StreamMessage{
		Type: "info",
		Data: fmt.Sprintf("Checkpoint created successfully at checkpoints/%s", version),
		Time: time.Now(),
	}

	// Send final completion message
	streamCh <- api.StreamMessage{
		Type: "complete",
		Data: fmt.Sprintf("Checkpoint %s created successfully", version),
		Time: time.Now(),
	}

	return nil
}

// RestoreWithStream restores the system from a checkpoint with streaming output
func (s *System) RestoreWithStream(ctx context.Context, checkpointID string, streamCh chan<- api.StreamMessage) error {
	defer close(streamCh)

	s.mu.Lock()
	s.restoringNow = true
	s.mu.Unlock()

	defer func() {
		s.mu.Lock()
		s.restoringNow = false
		s.mu.Unlock()
	}()

	s.logger.Info("Starting restore sequence", "checkpointID", checkpointID)

	// Stop process if running
	if s.IsProcessRunning() {
		streamCh <- api.StreamMessage{
			Type: "info",
			Data: "Stopping process for restore...",
			Time: time.Now(),
		}
		if err := s.StopProcess(); err != nil {
			s.logger.Error("Failed to stop process", "error", err)
			streamCh <- api.StreamMessage{
				Type:  "error",
				Error: fmt.Sprintf("Failed to stop process: %v", err),
				Time:  time.Now(),
			}
			return err
		}
		streamCh <- api.StreamMessage{
			Type: "info",
			Data: "Process stopped successfully",
			Time: time.Now(),
		}
	}

	// Perform JuiceFS restore with streaming
	if s.juicefs != nil {
		// The restore will create a checkpoint before restoring
		streamCh <- api.StreamMessage{
			Type: "info",
			Data: "Creating checkpoint before restore...",
			Time: time.Now(),
		}

		streamCh <- api.StreamMessage{
			Type: "info",
			Data: fmt.Sprintf("Restoring from checkpoint %s...", checkpointID),
			Time: time.Now(),
		}
		s.logger.Info("Restoring from checkpoint", "checkpointID", checkpointID)

		if err := s.juicefs.Restore(ctx, checkpointID); err != nil {
			s.logger.Error("Failed to restore checkpoint", "error", err)
			streamCh <- api.StreamMessage{
				Type:  "error",
				Error: fmt.Sprintf("Failed to restore checkpoint: %v", err),
				Time:  time.Now(),
			}
			return err
		}
		s.logger.Info("Checkpoint restored successfully")

		streamCh <- api.StreamMessage{
			Type: "info",
			Data: fmt.Sprintf("Restore from %s complete", checkpointID),
			Time: time.Now(),
		}
	}

	// Restart process
	streamCh <- api.StreamMessage{
		Type: "info",
		Data: "Starting process after restore...",
		Time: time.Now(),
	}
	s.logger.Info("Starting process after restore")
	if err := s.StartProcess(); err != nil {
		s.logger.Error("Failed to start process after restore", "error", err)
		streamCh <- api.StreamMessage{
			Type:  "error",
			Error: fmt.Sprintf("Failed to start process after restore: %v", err),
			Time:  time.Now(),
		}
		return err
	}

	s.logger.Info("Restore sequence completed")
	streamCh <- api.StreamMessage{
		Type: "complete",
		Data: fmt.Sprintf("Restore from %s complete", checkpointID),
		Time: time.Now(),
	}

	return nil
}

// ListCheckpoints returns a list of all available checkpoints
func (s *System) ListCheckpoints(ctx context.Context) ([]juicefs.CheckpointInfo, error) {
	if s.juicefs == nil {
		return nil, fmt.Errorf("JuiceFS not configured")
	}

	// Use reverse order (newest first) and include active at the top
	checkpoints, err := s.juicefs.ListCheckpointsWithActive(ctx)
	if err != nil {
		return nil, fmt.Errorf("failed to list checkpoints: %w", err)
	}

	// Also check for source info in the active directory
	if len(checkpoints) > 0 && s.config.JuiceFSBaseDir != "" {
		activeDir := filepath.Join(s.config.JuiceFSBaseDir, "data", "active")
		sourceFile := filepath.Join(activeDir, ".source")
		if sourceData, err := os.ReadFile(sourceFile); err == nil {
			// Find the active checkpoint (usually the newest) and mark its source
			sourceID := strings.TrimSpace(string(sourceData))
			// The active state doesn't have its own checkpoint, but we can indicate
			// what it was restored from
			s.logger.Info("Active directory was restored from checkpoint", "source", sourceID)
		}
	}

	return checkpoints, nil
}

// ListCheckpointsByHistory returns checkpoints that were restored from a specific version
func (s *System) ListCheckpointsByHistory(ctx context.Context, version string) ([]string, error) {
	if s.juicefs == nil {
		return nil, fmt.Errorf("JuiceFS not configured")
	}

	results, err := s.juicefs.ListCheckpointsWithHistory(ctx, version)
	if err != nil {
		return nil, fmt.Errorf("failed to list checkpoints by history: %w", err)
	}

	return results, nil
}

// GetCheckpoint returns information about a specific checkpoint
func (s *System) GetCheckpoint(ctx context.Context, checkpointID string) (*juicefs.CheckpointInfo, error) {
	if s.juicefs == nil {
		return nil, fmt.Errorf("JuiceFS not configured")
	}

	// Note: GetCurrentVersion() was removed in SQLite migration
	// The juicefs.GetCheckpoint() method now handles "active" checkpoint lookup internally
	checkpoint, err := s.juicefs.GetCheckpoint(ctx, checkpointID)
	if err != nil {
		return nil, fmt.Errorf("failed to get checkpoint: %w", err)
	}

	return checkpoint, nil
}

// ForwardSignal forwards a signal to the supervised process
func (s *System) ForwardSignal(sig os.Signal) error {
	s.mu.RLock()
	defer s.mu.RUnlock()

	if s.processRunning && s.supervisor != nil {
		return s.supervisor.Signal(sig)
	}
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

// HasJuiceFS returns whether JuiceFS is configured
func (s *System) HasJuiceFS() bool {
	return s.juicefs != nil
}

// Reaper delegation methods

// SubscribeToReapEvents delegates to the reaper
func (s *System) SubscribeToReapEvents() <-chan int {
	if s.reaper != nil {
		return s.reaper.SubscribeToEvents()
	}
	// Return a closed channel if no reaper
	ch := make(chan int)
	close(ch)
	return ch
}

// UnsubscribeFromReapEvents delegates to the reaper
func (s *System) UnsubscribeFromReapEvents(ch <-chan int) {
	if s.reaper != nil {
		s.reaper.UnsubscribeFromEvents(ch)
	}
}

// WasProcessReaped delegates to the reaper
func (s *System) WasProcessReaped(pid int) (bool, time.Time) {
	if s.reaper != nil {
		return s.reaper.WasProcessReaped(pid)
	}
	return false, time.Time{}
}
