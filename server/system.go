package main

import (
	"context"
	"fmt"
	"lib/api"
	"log/slog"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"time"

	"github.com/fly-dev-env/sprite-env/server/packages/juicefs"
	"github.com/sprite-env/server/packages/supervisor"
)

// System encapsulates the JuiceFS and supervised process management
type System struct {
	config     SystemConfig
	logger     *slog.Logger
	juicefs    *juicefs.JuiceFS
	supervisor *supervisor.Supervisor
	reaper     *Reaper

	// Channels for monitoring
	processDoneCh chan error

	// State management
	mu             sync.RWMutex
	processRunning bool
	restoringNow   bool
}

// SystemConfig holds configuration for the System
type SystemConfig struct {
	// Process configuration
	ProcessCommand                 []string
	ProcessWorkingDir              string
	ProcessEnvironment             []string
	ProcessGracefulShutdownTimeout time.Duration

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
}

// NewSystem creates a new System instance
func NewSystem(config SystemConfig, logger *slog.Logger, reaper *Reaper) (*System, error) {
	s := &System{
		config:        config,
		logger:        logger,
		reaper:        reaper,
		processDoneCh: make(chan error, 1),
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
	// Start JuiceFS if configured
	if s.juicefs != nil {
		s.logger.Info("Starting JuiceFS...")
		if err := s.juicefs.Start(ctx); err != nil {
			return fmt.Errorf("failed to start JuiceFS: %w", err)
		}
		s.logger.Info("JuiceFS started successfully")
	}

	// Start supervised process if configured
	if len(s.config.ProcessCommand) > 0 {
		s.logger.Info("Starting supervised process...")
		if err := s.StartProcess(); err != nil {
			// If process fails to start, stop JuiceFS
			if s.juicefs != nil {
				stopCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
				defer cancel()
				s.juicefs.Stop(stopCtx)
			}
			return fmt.Errorf("failed to start process: %w", err)
		}
	}

	return nil
}

// StartProcess starts the supervised process
func (s *System) StartProcess() error {
	s.mu.Lock()
	defer s.mu.Unlock()

	if len(s.config.ProcessCommand) == 0 {
		return fmt.Errorf("no process command configured")
	}

	// Set up process working directory
	workingDir := s.config.ProcessWorkingDir
	if s.juicefs != nil && workingDir == "" {
		// Default to JuiceFS active directory if available
		workingDir = filepath.Join(s.config.JuiceFSBaseDir, "data", "active", "fs")
	}

	supervisorConfig := supervisor.Config{
		Command:     s.config.ProcessCommand[0],
		Args:        s.config.ProcessCommand[1:],
		GracePeriod: s.config.ProcessGracefulShutdownTimeout,
		Env:         append(os.Environ(), s.config.ProcessEnvironment...),
		Dir:         workingDir,
	}

	sup, err := supervisor.New(supervisorConfig)
	if err != nil {
		return fmt.Errorf("failed to create supervisor: %w", err)
	}

	pid, err := sup.Start()
	if err != nil {
		return fmt.Errorf("failed to start process: %w", err)
	}

	s.supervisor = sup
	s.processRunning = true

	s.logger.Info("Process started", "pid", pid, "command", s.config.ProcessCommand)

	// Monitor process in background
	go func() {
		err := s.supervisor.Wait()
		s.processDoneCh <- err

		s.mu.Lock()
		s.processRunning = false
		s.mu.Unlock()
	}()

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
	if err := s.supervisor.Stop(); err != nil {
		return fmt.Errorf("failed to stop process: %w", err)
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

// IsRestoring returns whether the system is currently restoring
func (s *System) IsRestoring() bool {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return s.restoringNow
}

// Checkpoint creates a checkpoint of the current system state
func (s *System) Checkpoint(ctx context.Context, checkpointID string) error {
	if checkpointID == "" {
		return fmt.Errorf("checkpoint ID is required")
	}

	if s.juicefs == nil {
		return fmt.Errorf("JuiceFS not configured")
	}

	// Use the proper JuiceFS checkpoint method that handles overlay
	if err := s.juicefs.Checkpoint(ctx, checkpointID); err != nil {
		return fmt.Errorf("failed to create checkpoint: %w", err)
	}

	s.logger.Info("Checkpoint created successfully", "checkpointID", checkpointID)
	return nil
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

	if checkpointID == "" {
		return fmt.Errorf("checkpoint ID is required")
	}

	if s.juicefs == nil {
		return fmt.Errorf("JuiceFS not configured")
	}

	// Send initial message
	streamCh <- api.StreamMessage{
		Type: "info",
		Data: fmt.Sprintf("Creating checkpoint %s...", checkpointID),
		Time: time.Now(),
	}

	// Use the proper JuiceFS checkpoint method that handles overlay
	if err := s.juicefs.Checkpoint(ctx, checkpointID); err != nil {
		streamCh <- api.StreamMessage{
			Type:  "error",
			Error: fmt.Sprintf("Failed to create checkpoint: %v", err),
			Time:  time.Now(),
		}
		return err
	}

	streamCh <- api.StreamMessage{
		Type: "info",
		Data: fmt.Sprintf("Checkpoint created successfully at checkpoints/%s", checkpointID),
		Time: time.Now(),
	}

	// Send final completion message
	streamCh <- api.StreamMessage{
		Type: "complete",
		Data: fmt.Sprintf("Checkpoint %s created successfully", checkpointID),
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

	checkpoints, err := s.juicefs.ListCheckpoints(ctx)
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

// GetCheckpoint returns information about a specific checkpoint
func (s *System) GetCheckpoint(ctx context.Context, checkpointID string) (*juicefs.CheckpointInfo, error) {
	if s.juicefs == nil {
		return nil, fmt.Errorf("JuiceFS not configured")
	}

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
