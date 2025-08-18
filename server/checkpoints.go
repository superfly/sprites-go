package main

import (
	"context"
	"fmt"
	"os"
	"path/filepath"
	"time"

	"github.com/sprite-env/lib/api"
	"github.com/superfly/sprite-env/packages/juicefs"
)

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
	s.setState("restoringNow", true)

	defer func() {
		s.setState("restoringNow", false)
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

	s.setState("restoringNow", true)

	defer func() {
		s.setState("restoringNow", false)
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

	// Use basic listing for fast performance
	checkpoints, err := s.juicefs.ListCheckpointsWithActive(ctx)
	if err != nil {
		return nil, fmt.Errorf("failed to list checkpoints: %w", err)
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

// ResetState resets the system state by:
// 1. Stopping the process if running
// 2. Clearing the JuiceFS mount directory
// 3. Removing the checkpoint database
func (s *System) ResetState() error {
	s.setState("restoringNow", true)

	defer func() {
		s.setState("restoringNow", false)
	}()

	s.logger.Info("Starting system state reset")

	// Stop the process if it's running
	if err := s.StopProcess(); err != nil {
		return fmt.Errorf("failed to stop process: %w", err)
	}

	// Only proceed with cleanup if JuiceFS is configured
	if s.juicefs == nil {
		s.logger.Info("JuiceFS not configured, nothing to reset")
		return nil
	}

	// Clean up JuiceFS data directories
	activeDir := filepath.Join(s.config.JuiceFSBaseDir, "data", "active")
	checkpointsDir := filepath.Join(s.config.JuiceFSBaseDir, "data", "checkpoints")
	checkpointDBPath := filepath.Join(s.config.JuiceFSBaseDir, "checkpoints.db")

	// Remove all contents of active directory (but keep the directory itself)
	s.logger.Info("Cleaning active directory", "path", activeDir)
	if entries, err := os.ReadDir(activeDir); err == nil {
		for _, entry := range entries {
			entryPath := filepath.Join(activeDir, entry.Name())
			s.logger.Debug("Removing", "path", entryPath)
			if err := os.RemoveAll(entryPath); err != nil {
				s.logger.Error("Failed to remove entry", "path", entryPath, "error", err)
				return fmt.Errorf("failed to remove %s: %w", entryPath, err)
			}
		}
	} else if !os.IsNotExist(err) {
		s.logger.Error("Failed to read active directory", "path", activeDir, "error", err)
		return fmt.Errorf("failed to read active directory: %w", err)
	}

	// Remove all contents of checkpoints directory (but keep the directory itself)
	s.logger.Info("Cleaning checkpoints directory", "path", checkpointsDir)
	if entries, err := os.ReadDir(checkpointsDir); err == nil {
		for _, entry := range entries {
			entryPath := filepath.Join(checkpointsDir, entry.Name())
			s.logger.Debug("Removing", "path", entryPath)
			if err := os.RemoveAll(entryPath); err != nil {
				s.logger.Error("Failed to remove entry", "path", entryPath, "error", err)
				return fmt.Errorf("failed to remove %s: %w", entryPath, err)
			}
		}
	} else if !os.IsNotExist(err) {
		s.logger.Error("Failed to read checkpoints directory", "path", checkpointsDir, "error", err)
		return fmt.Errorf("failed to read checkpoints directory: %w", err)
	}

	s.logger.Info("Removing checkpoint database", "path", checkpointDBPath)
	if err := os.Remove(checkpointDBPath); err != nil && !os.IsNotExist(err) {
		s.logger.Error("Failed to remove checkpoint database", "path", checkpointDBPath, "error", err)
		return fmt.Errorf("failed to remove checkpoint database: %w", err)
	}

	// Also remove the checkpoint database WAL file if it exists
	walPath := checkpointDBPath + "-wal"
	if err := os.Remove(walPath); err != nil && !os.IsNotExist(err) {
		s.logger.Warn("Failed to remove checkpoint database WAL", "path", walPath, "error", err)
	}

	// Remove the checkpoint database SHM file if it exists
	shmPath := checkpointDBPath + "-shm"
	if err := os.Remove(shmPath); err != nil && !os.IsNotExist(err) {
		s.logger.Warn("Failed to remove checkpoint database SHM", "path", shmPath, "error", err)
	}

	s.logger.Info("System state reset completed successfully")

	// Start the process back up
	s.logger.Info("Starting process after reset")
	if err := s.StartProcess(); err != nil {
		return fmt.Errorf("failed to start process after reset: %w", err)
	}

	return nil
}
