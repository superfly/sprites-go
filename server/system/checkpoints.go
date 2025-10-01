package system

import (
	"context"
	"fmt"
	"os"
	"path/filepath"
	"time"

	"github.com/superfly/sprite-env/lib/api"
)

// Checkpoint creates a checkpoint of the current system state
func (s *System) Checkpoint(ctx context.Context, checkpointID string) error {
	if s.CheckpointManager == nil {
		return fmt.Errorf("checkpoint manager not configured")
	}
	if _, err := s.CheckpointManager.Checkpoint(ctx); err != nil {
		return fmt.Errorf("failed to create checkpoint: %w", err)
	}
	s.logger.Info("Checkpoint created successfully")
	return nil
}

// CheckpointAndGetVersion creates a checkpoint and returns the version used
func (s *System) CheckpointAndGetVersion(ctx context.Context) (string, error) {
	if s.JuiceFS == nil {
		return "", fmt.Errorf("JuiceFS not configured")
	}

	// Generate checkpoint ID
	checkpointID := fmt.Sprintf("checkpoint-%d", time.Now().Unix())

	if err := s.Checkpoint(ctx, checkpointID); err != nil {
		return "", err
	}

	return checkpointID, nil
}

// Restore restores the system from a checkpoint
func (s *System) Restore(ctx context.Context, checkpointID string) error {

	if checkpointID == "" {
		return fmt.Errorf("checkpoint ID is required")
	}

	if s.CheckpointManager == nil {
		return fmt.Errorf("checkpoint manager not configured")
	}

	s.logger.Info("Starting restore sequence", "checkpointID", checkpointID)

	// Checkpoint manager handles shutdown/boot via restore prep function
	if err := s.CheckpointManager.Restore(ctx, checkpointID); err != nil {
		return fmt.Errorf("failed to restore checkpoint: %w", err)
	}

	s.logger.Info("Restore sequence completed")
	return nil
}

// CheckpointWithStream creates a checkpoint with streaming output
func (s *System) CheckpointWithStream(ctx context.Context, checkpointID string, streamCh chan<- api.StreamMessage) error {
	defer close(streamCh)

	if s.JuiceFS == nil {
		return fmt.Errorf("JuiceFS not configured")
	}

	// Send initial message
	streamCh <- api.StreamMessage{
		Type: "info",
		Data: "Creating checkpoint...",
		Time: time.Now(),
	}

	// Create the checkpoint
	if err := s.Checkpoint(ctx, checkpointID); err != nil {
		streamCh <- api.StreamMessage{
			Type:  "error",
			Error: fmt.Sprintf("Failed to create checkpoint: %v", err),
			Time:  time.Now(),
		}
		return err
	}

	version := checkpointID

	streamCh <- api.StreamMessage{
		Type: "info",
		Data: fmt.Sprintf("Checkpoint created successfully at checkpoints/%s", version),
		Time: time.Now(),
	}

	// Send notification to admin channel
	if s.AdminChannel != nil {
		s.AdminChannel.SendActivityEvent("checkpoint_created", map[string]interface{}{
			"timestamp": time.Now().Unix(),
			"version":   version,
			"path":      fmt.Sprintf("checkpoints/%s", version),
		})
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

	s.logger.Info("Starting restore sequence", "checkpointID", checkpointID)

	// Shutdown container components
	streamCh <- api.StreamMessage{
		Type: "info",
		Data: "Shutting down container components...",
		Time: time.Now(),
	}
	if err := s.ShutdownContainer(ctx); err != nil {
		s.logger.Error("Failed to shutdown container for restore", "error", err)
		streamCh <- api.StreamMessage{
			Type: "warning",
			Data: fmt.Sprintf("Failed to shutdown container components: %v", err),
			Time: time.Now(),
		}
		// Continue with restore even if container shutdown fails
	} else {
		streamCh <- api.StreamMessage{
			Type: "info",
			Data: "Container components stopped successfully",
			Time: time.Now(),
		}
	}

	// Send notification to admin channel that restore is starting
	if s.AdminChannel != nil {
		s.AdminChannel.SendActivityEvent("restore_started", map[string]interface{}{
			"timestamp":     time.Now().Unix(),
			"checkpoint_id": checkpointID,
		})
	}

	// Perform Restore via CheckpointManager with streaming notifications
	streamCh <- api.StreamMessage{Type: "info", Data: "Shutting down container...", Time: time.Now()}
	streamCh <- api.StreamMessage{Type: "info", Data: fmt.Sprintf("Restoring from checkpoint %s...", checkpointID), Time: time.Now()}
	s.logger.Info("Restoring from checkpoint", "checkpointID", checkpointID)

	if err := s.Restore(ctx, checkpointID); err != nil {
		s.logger.Error("Failed to restore checkpoint", "error", err)
		streamCh <- api.StreamMessage{Type: "error", Error: fmt.Sprintf("Failed to restore checkpoint: %v", err), Time: time.Now()}
		return err
	}

	s.logger.Info("Checkpoint restored successfully")
	streamCh <- api.StreamMessage{Type: "info", Data: "Container components started successfully", Time: time.Now()}

	s.logger.Info("Restore sequence completed")

	// Send notification to admin channel that restore is completed
	if s.AdminChannel != nil {
		s.AdminChannel.SendActivityEvent("restore_completed", map[string]interface{}{
			"timestamp":     time.Now().Unix(),
			"checkpoint_id": checkpointID,
		})
	}

	streamCh <- api.StreamMessage{
		Type: "complete",
		Data: fmt.Sprintf("Restore from %s complete", checkpointID),
		Time: time.Now(),
	}

	return nil
}

// ListCheckpoints returns a list of all available checkpoints
func (s *System) ListCheckpoints(ctx context.Context) ([]api.CheckpointInfo, error) {
	if s.CheckpointManager == nil {
		return nil, fmt.Errorf("checkpoint manager not configured")
	}
	latest, err := s.CheckpointManager.GetLatest()
	if err != nil {
		return nil, fmt.Errorf("get latest checkpoint: %w", err)
	}
	records, err := s.CheckpointManager.ListAll()
	if err != nil {
		return nil, fmt.Errorf("list checkpoints: %w", err)
	}
	var out []api.CheckpointInfo
	out = append(out, api.CheckpointInfo{ID: "Current", CreateTime: latest.CreatedAt})
	for _, r := range records {
		out = append(out, api.CheckpointInfo{ID: filepath.Base(r.Path), CreateTime: r.CreatedAt})
	}
	return out, nil
}

// ListCheckpointsByHistory returns checkpoints that were restored from a specific version
func (s *System) ListCheckpointsByHistory(ctx context.Context, version string) ([]string, error) {
	// History tracking not implemented in SQLite-backed checkpoint DB yet
	return []string{}, nil
}

// GetCheckpoint returns information about a specific checkpoint
func (s *System) GetCheckpoint(ctx context.Context, checkpointID string) (*api.CheckpointInfo, error) {
	if s.CheckpointManager == nil {
		return nil, fmt.Errorf("checkpoint manager not configured")
	}
	// Handle special "active" checkpoint ID via latest record
	if checkpointID == "active" || checkpointID == "Current" {
		latest, err := s.CheckpointManager.GetLatest()
		if err != nil {
			return nil, fmt.Errorf("failed to get latest checkpoint: %w", err)
		}
		return &api.CheckpointInfo{ID: filepath.Base(latest.Path), CreateTime: latest.CreatedAt}, nil
	}
	rec, err := s.CheckpointManager.FindByIdentifier(checkpointID)
	if err != nil {
		return nil, fmt.Errorf("failed to get checkpoint: %w", err)
	}
	return &api.CheckpointInfo{ID: filepath.Base(rec.Path), CreateTime: rec.CreatedAt}, nil
}

// ResetState resets the system state by:
// 1. Stopping the process if running
// 2. Clearing the JuiceFS mount directory
// 3. Removing the checkpoint database
func (s *System) ResetState() error {

	s.logger.Info("Starting system state reset")

	// Stop the process if it's running
	if err := s.StopProcess(); err != nil {
		return fmt.Errorf("failed to stop process: %w", err)
	}

	// Stop all services
	if s.ServicesManager != nil {
		s.logger.Info("Stopping all services during reset")
		if err := s.ServicesManager.Shutdown(); err != nil {
			s.logger.Error("Failed to stop services during reset", "error", err)
			// Continue with reset even if service shutdown fails
		}
	}

	// Only proceed with cleanup if JuiceFS is configured
	if s.JuiceFS == nil {
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
