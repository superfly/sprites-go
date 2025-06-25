package juicefs

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"time"
)

// CheckpointInfo contains information about a checkpoint
type CheckpointInfo struct {
	ID         string    `json:"id"`
	CreateTime time.Time `json:"create_time"`
	SourceID   string    `json:"source_id,omitempty"` // If this was restored from another checkpoint
	History    []string  `json:"history,omitempty"`   // Restore history from .history file
}

// Checkpoint creates a checkpoint of the active directory using SQLite
func (j *JuiceFS) Checkpoint(ctx context.Context, checkpointID string) error {
	if j.checkpointDB == nil {
		return fmt.Errorf("checkpoint database not initialized")
	}

	mountPath := filepath.Join(j.config.BaseDir, "data")
	checkpointsDir := filepath.Join(mountPath, "checkpoints")

	// Ensure checkpoints directory exists
	if err := os.MkdirAll(checkpointsDir, 0755); err != nil {
		return fmt.Errorf("failed to create checkpoints directory: %w", err)
	}

	// Prepare overlay for checkpoint (sync and freeze)
	if j.overlayMgr != nil {
		if err := j.overlayMgr.PrepareForCheckpoint(ctx); err != nil {
			return fmt.Errorf("failed to prepare overlay for checkpoint: %w", err)
		}

		// Ensure we unfreeze the overlay even if the clone fails
		defer func() {
			if unfreezeErr := j.overlayMgr.UnfreezeAfterCheckpoint(ctx); unfreezeErr != nil {
				j.logger.Warn("Failed to unfreeze overlay", "error", unfreezeErr)
			}
		}()
	}

	// Create checkpoint using the database transaction
	record, err := j.checkpointDB.CreateCheckpoint(
		// Clone function
		func(src, dst string) error {
			// Convert relative paths to absolute paths
			srcPath := filepath.Join(mountPath, src)
			dstPath := filepath.Join(mountPath, dst)

			j.logger.Info("Creating checkpoint: cloning", "src", src, "dst", dst)
			cloneCmd := exec.CommandContext(ctx, "juicefs", "clone", srcPath, dstPath)
			if output, err := cloneCmd.CombinedOutput(); err != nil {
				return fmt.Errorf("failed to clone: %w, output: %s", err, string(output))
			}
			return nil
		},
		// Rename function (also handles cleanup when dst is empty)
		func(src, dst string) error {
			srcPath := filepath.Join(mountPath, src)

			if dst == "" {
				// Cleanup request
				j.logger.Info("Cleaning up temporary checkpoint directory", "path", srcPath)
				return os.RemoveAll(srcPath)
			}

			dstPath := filepath.Join(mountPath, dst)
			j.logger.Info("Finalizing checkpoint: renaming", "src", src, "dst", dst)
			return os.Rename(srcPath, dstPath)
		},
	)

	if err != nil {
		return fmt.Errorf("failed to create checkpoint: %w", err)
	}

	j.logger.Info("Checkpoint created successfully", "id", record.ID, "path", record.Path)
	return nil
}

// CheckpointWithVersion creates a checkpoint and returns the version used
func (j *JuiceFS) CheckpointWithVersion(ctx context.Context) (string, error) {
	if j.checkpointDB == nil {
		return "", fmt.Errorf("checkpoint database not initialized")
	}

	// Get the current latest checkpoint to determine what the new version will be
	latest, err := j.checkpointDB.GetLatestCheckpoint()
	if err != nil {
		return "", fmt.Errorf("failed to get latest checkpoint: %w", err)
	}

	// The new checkpoint will have ID = latest.ID + 1, but represents version = latest.ID - 1
	// (since IDs start at 1 but versions start at 0)
	newVersion := fmt.Sprintf("v%d", latest.ID-1)

	// Create the checkpoint
	err = j.Checkpoint(ctx, "")
	if err != nil {
		return "", err
	}

	return newVersion, nil
}

// Restore restores from a checkpoint using SQLite
func (j *JuiceFS) Restore(ctx context.Context, checkpointID string) error {
	if checkpointID == "" {
		return fmt.Errorf("checkpoint ID is required")
	}

	if j.checkpointDB == nil {
		return fmt.Errorf("checkpoint database not initialized")
	}

	mountPath := filepath.Join(j.config.BaseDir, "data")
	activeDir := filepath.Join(mountPath, "active")
	checkpointsDir := filepath.Join(mountPath, "checkpoints")

	// Look up the checkpoint in the database
	var checkpointPath string
	var record *CheckpointRecord
	var err error

	// Check if the checkpointID is a path like "checkpoints/v3" or just "v3" or "3"
	if strings.HasPrefix(checkpointID, "checkpoints/v") {
		// Full path provided
		checkpointPath = checkpointID
	} else if strings.HasPrefix(checkpointID, "v") {
		// Version string like "v3"
		checkpointPath = filepath.Join("checkpoints", checkpointID)
	} else if id, err := strconv.ParseInt(checkpointID, 10, 64); err == nil {
		// Numeric ID provided
		record, err = j.checkpointDB.GetCheckpointByID(id)
		if err != nil {
			return fmt.Errorf("checkpoint %d not found: %w", id, err)
		}
		checkpointPath = record.Path
	} else {
		// Try to find by path
		checkpointPath = filepath.Join("checkpoints", checkpointID)
	}

	// If we don't have the record yet, look it up by path
	if record == nil {
		record, err = j.checkpointDB.FindCheckpointByPath(checkpointPath)
		if err != nil {
			return fmt.Errorf("checkpoint not found in database: %w", err)
		}
	}

	fullCheckpointPath := filepath.Join(mountPath, checkpointPath)
	if _, err := os.Stat(fullCheckpointPath); os.IsNotExist(err) {
		return fmt.Errorf("checkpoint directory does not exist at %s", fullCheckpointPath)
	}

	// Handle overlay if present
	if j.overlayMgr != nil {
		// First sync and freeze the overlay (same as checkpoint)
		if err := j.overlayMgr.PrepareForCheckpoint(ctx); err != nil {
			// If prepare fails, it might be because overlay is not mounted, which is ok
			j.logger.Debug("Could not prepare overlay for restore", "error", err)
		} else {
			// Unfreeze after sync
			if err := j.overlayMgr.UnfreezeAfterCheckpoint(ctx); err != nil {
				j.logger.Warn("Failed to unfreeze overlay", "error", err)
			}
		}

		// Unmount the overlay before restore
		if err := j.overlayMgr.Unmount(ctx); err != nil {
			j.logger.Warn("Failed to unmount overlay", "error", err)
		}
	}

	// If active directory exists, back it up
	if _, err := os.Stat(activeDir); err == nil {
		timestamp := time.Now().UnixNano()
		backupName := fmt.Sprintf("pre-restore-v%d-%d", record.ID, timestamp)
		backupPath := filepath.Join(checkpointsDir, backupName)

		j.logger.Info("Backing up current active directory", "backupPath", backupPath)
		if err := os.Rename(activeDir, backupPath); err != nil {
			return fmt.Errorf("failed to backup active directory: %w", err)
		}
		j.logger.Info("Backup completed")
	}

	// Clone checkpoint to active directory
	j.logger.Info("Restoring from checkpoint", "version", record.ID, "path", checkpointPath)
	cloneCmd := exec.CommandContext(ctx, "juicefs", "clone", fullCheckpointPath, activeDir)
	if output, err := cloneCmd.CombinedOutput(); err != nil {
		return fmt.Errorf("failed to restore from checkpoint: %w, output: %s", err, string(output))
	}

	// Mount the overlay from the restored active directory
	if j.overlayMgr != nil {
		// Update the image path to point to the restored active directory
		j.overlayMgr.UpdateImagePath()

		j.logger.Info("Mounting overlay from restored checkpoint...")
		j.logger.Info("New image path", "path", j.overlayMgr.GetImagePath())

		// Mount the overlay
		if err := j.overlayMgr.Mount(ctx); err != nil {
			// Log error but don't fail the restore
			j.logger.Warn("Failed to mount overlay after restore", "error", err)
		}
	}

	// Apply quota asynchronously after restore
	go j.applyActiveFsQuota()

	j.logger.Info("Restore from checkpoint complete", "version", record.ID)
	return nil
}

// ListCheckpoints returns a list of all available checkpoints from SQLite
func (j *JuiceFS) ListCheckpoints(ctx context.Context) ([]CheckpointInfo, error) {
	if j.checkpointDB == nil {
		return nil, fmt.Errorf("checkpoint database not initialized")
	}

	// Get all checkpoints from database
	rows, err := j.checkpointDB.db.Query(`
		SELECT id, path, parent_id, created_at 
		FROM sprite_checkpoints 
		WHERE path LIKE 'checkpoints/%'
		ORDER BY id DESC
	`)
	if err != nil {
		return nil, fmt.Errorf("failed to query checkpoints: %w", err)
	}
	defer rows.Close()

	var checkpoints []CheckpointInfo
	for rows.Next() {
		var record CheckpointRecord
		if err := rows.Scan(&record.ID, &record.Path, &record.ParentID, &record.CreatedAt); err != nil {
			continue // Skip invalid rows
		}

		// Convert path like "checkpoints/v3" to version ID "v3"
		versionID := filepath.Base(record.Path)

		checkpoint := CheckpointInfo{
			ID:         versionID,
			CreateTime: record.CreatedAt,
		}
		checkpoints = append(checkpoints, checkpoint)
	}

	return checkpoints, nil
}

// ListCheckpointsReverse returns checkpoints sorted by creation time in reverse order (newest first)
func (j *JuiceFS) ListCheckpointsReverse(ctx context.Context) ([]CheckpointInfo, error) {
	checkpoints, err := j.ListCheckpoints(ctx)
	if err != nil {
		return nil, err
	}

	// Sort by creation time in reverse order
	for i := 0; i < len(checkpoints)-1; i++ {
		for k := i + 1; k < len(checkpoints); k++ {
			if checkpoints[i].CreateTime.Before(checkpoints[k].CreateTime) {
				checkpoints[i], checkpoints[k] = checkpoints[k], checkpoints[i]
			}
		}
	}

	return checkpoints, nil
}

// ListCheckpointsWithActive returns checkpoints including the active state at the top
func (j *JuiceFS) ListCheckpointsWithActive(ctx context.Context) ([]CheckpointInfo, error) {
	// Get regular checkpoints first
	checkpoints, err := j.ListCheckpointsReverse(ctx)
	if err != nil {
		return nil, err
	}

	// Get active info
	activeInfo, err := j.GetCheckpoint(ctx, "active")
	if err != nil {
		// If we can't get active info, just return checkpoints
		return checkpoints, nil
	}

	// Mark the active checkpoint ID with " (active)" suffix
	activeInfo.ID = activeInfo.ID + " (active)"

	// Prepend active to the list
	result := make([]CheckpointInfo, 0, len(checkpoints)+1)
	result = append(result, *activeInfo)
	result = append(result, checkpoints...)

	return result, nil
}

// ListCheckpointsWithHistory returns checkpoints that have the specified version in their history
func (j *JuiceFS) ListCheckpointsWithHistory(ctx context.Context, version string) ([]string, error) {
	if j.checkpointDB == nil {
		return nil, fmt.Errorf("checkpoint database not initialized")
	}

	// For SQLite implementation, we could track parent relationships
	// For now, return empty list as this feature needs to be redesigned for SQLite
	return []string{}, nil
}

// GetCheckpoint returns information about a specific checkpoint
func (j *JuiceFS) GetCheckpoint(ctx context.Context, checkpointID string) (*CheckpointInfo, error) {
	if j.checkpointDB == nil {
		return nil, fmt.Errorf("checkpoint database not initialized")
	}

	// Handle special "active" checkpoint ID
	if checkpointID == "active" {
		// Get the latest checkpoint (which represents the current active state)
		latest, err := j.checkpointDB.GetLatestCheckpoint()
		if err != nil {
			return nil, fmt.Errorf("failed to get latest checkpoint: %w", err)
		}

		checkpoint := &CheckpointInfo{
			ID:         fmt.Sprintf("v%d", latest.ID-1), // Convert DB ID to version
			CreateTime: latest.CreatedAt,
		}

		return checkpoint, nil
	}

	// Look up specific checkpoint
	var record *CheckpointRecord
	var err error

	if strings.HasPrefix(checkpointID, "v") {
		// Version string like "v3" - look up by path
		checkpointPath := filepath.Join("checkpoints", checkpointID)
		record, err = j.checkpointDB.FindCheckpointByPath(checkpointPath)
	} else if id, parseErr := strconv.ParseInt(checkpointID, 10, 64); parseErr == nil {
		// Numeric ID provided
		record, err = j.checkpointDB.GetCheckpointByID(id)
	} else {
		return nil, fmt.Errorf("invalid checkpoint ID format: %s", checkpointID)
	}

	if err != nil {
		return nil, fmt.Errorf("checkpoint %s not found: %w", checkpointID, err)
	}

	// Convert path like "checkpoints/v3" to version ID "v3"
	versionID := filepath.Base(record.Path)

	checkpoint := &CheckpointInfo{
		ID:         versionID,
		CreateTime: record.CreatedAt,
	}

	return checkpoint, nil
}
