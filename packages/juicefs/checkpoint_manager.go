package juicefs

import (
	"context"
	"fmt"
	"io"
	"log/slog"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"time"
)

// CheckpointManager handles all checkpoint and restore operations for JuiceFS
type CheckpointManager struct {
	baseDir    string
	db         *CheckpointDB
	overlayMgr *OverlayManager
	logger     *slog.Logger
}

// NewCheckpointManager creates a new checkpoint manager
func NewCheckpointManager(baseDir string, overlayMgr *OverlayManager, logger *slog.Logger) *CheckpointManager {
	// Create a no-op logger if none provided
	if logger == nil {
		logger = slog.New(slog.NewTextHandler(io.Discard, nil))
	}

	return &CheckpointManager{
		baseDir:    baseDir,
		overlayMgr: overlayMgr,
		logger:     logger,
	}
}

// Initialize sets up the checkpoint database
func (cm *CheckpointManager) Initialize(mountPath string) error {
	db, err := NewCheckpointDB(CheckpointDBConfig{
		BaseDir: mountPath,
		Logger:  cm.logger,
	})
	if err != nil {
		return fmt.Errorf("failed to initialize checkpoint database: %w", err)
	}
	cm.db = db
	return nil
}

// Close closes the checkpoint database
func (cm *CheckpointManager) Close() error {
	if cm.db != nil {
		return cm.db.Close()
	}
	return nil
}

// Checkpoint creates a checkpoint of the active directory
func (cm *CheckpointManager) Checkpoint(ctx context.Context, checkpointID string) error {
	// Note: checkpointID parameter is ignored in the new implementation
	// as we use auto-incrementing IDs from the database

	if cm.db == nil {
		return fmt.Errorf("checkpoint database not initialized")
	}

	mountPath := filepath.Join(cm.baseDir, "data")
	checkpointsDir := filepath.Join(mountPath, "checkpoints")

	// Ensure checkpoints directory exists
	if err := os.MkdirAll(checkpointsDir, 0755); err != nil {
		return fmt.Errorf("failed to create checkpoints directory: %w", err)
	}

	// Prepare overlay for checkpoint (sync and freeze)
	if cm.overlayMgr != nil {
		if err := cm.overlayMgr.PrepareForCheckpoint(ctx); err != nil {
			return fmt.Errorf("failed to prepare overlay for checkpoint: %w", err)
		}

		// Ensure we unfreeze the overlay even if the clone fails
		defer func() {
			if unfreezeErr := cm.overlayMgr.UnfreezeAfterCheckpoint(ctx); unfreezeErr != nil {
				cm.logger.Warn("Failed to unfreeze overlay", "error", unfreezeErr)
			}
		}()
	}

	// Create checkpoint using the database transaction
	record, err := cm.db.CreateCheckpoint(
		// Clone function
		func(src, dst string) error {
			// Convert relative paths to absolute paths
			srcPath := filepath.Join(mountPath, src)
			dstPath := filepath.Join(mountPath, dst)

			cm.logger.Info("Creating checkpoint", "src", src, "dst", dst)
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
				cm.logger.Debug("Cleaning up temporary checkpoint directory", "path", srcPath)
				return os.RemoveAll(srcPath)
			}

			dstPath := filepath.Join(mountPath, dst)
			cm.logger.Debug("Finalizing checkpoint", "src", src, "dst", dst)
			return os.Rename(srcPath, dstPath)
		},
	)

	if err != nil {
		return fmt.Errorf("failed to create checkpoint: %w", err)
	}

	cm.logger.Info("Checkpoint created successfully", "id", record.ID, "path", record.Path)
	return nil
}

// Restore restores from a checkpoint
func (cm *CheckpointManager) Restore(ctx context.Context, checkpointID string) error {
	if checkpointID == "" {
		return fmt.Errorf("checkpoint ID is required")
	}

	if cm.db == nil {
		return fmt.Errorf("checkpoint database not initialized")
	}

	mountPath := filepath.Join(cm.baseDir, "data")
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
		record, err = cm.db.GetCheckpointByID(id)
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
		record, err = cm.db.FindCheckpointByPath(checkpointPath)
		if err != nil {
			return fmt.Errorf("checkpoint not found in database: %w", err)
		}
	}

	fullCheckpointPath := filepath.Join(mountPath, checkpointPath)
	if _, err := os.Stat(fullCheckpointPath); os.IsNotExist(err) {
		return fmt.Errorf("checkpoint directory does not exist at %s", fullCheckpointPath)
	}

	// Handle overlay if present
	if cm.overlayMgr != nil {
		// First sync and freeze the overlay (same as checkpoint)
		if err := cm.overlayMgr.PrepareForCheckpoint(ctx); err != nil {
			// If prepare fails, it might be because overlay is not mounted, which is ok
			cm.logger.Debug("Could not prepare overlay for restore", "error", err)
		} else {
			// Unfreeze after sync
			if err := cm.overlayMgr.UnfreezeAfterCheckpoint(ctx); err != nil {
				cm.logger.Warn("Failed to unfreeze overlay", "error", err)
			}
		}

		// Unmount the overlay before restore - error if this fails
		if err := cm.overlayMgr.Unmount(ctx); err != nil {
			return fmt.Errorf("failed to unmount overlay before restore: %w", err)
		}
	}

	// If active directory exists, back it up
	if _, err := os.Stat(activeDir); err == nil {
		timestamp := time.Now().Unix()
		backupName := fmt.Sprintf("pre-restore-v%d-%d", record.ID, timestamp)
		backupPath := filepath.Join(checkpointsDir, backupName)

		cm.logger.Info("Backing up current active directory", "backupPath", backupPath)
		if err := os.Rename(activeDir, backupPath); err != nil {
			return fmt.Errorf("failed to backup active directory: %w", err)
		}
		cm.logger.Info("Backup completed")
	}

	// Clone checkpoint to active directory
	cm.logger.Info("Restoring from checkpoint", "id", record.ID, "path", checkpointPath)
	cloneCmd := exec.CommandContext(ctx, "juicefs", "clone", fullCheckpointPath, activeDir)
	if output, err := cloneCmd.CombinedOutput(); err != nil {
		return fmt.Errorf("failed to restore from checkpoint: %w, output: %s", err, string(output))
	}

	// Mount the overlay from the restored active directory
	if cm.overlayMgr != nil {
		// Update the image path to point to the restored active directory
		cm.overlayMgr.UpdateImagePath()

		cm.logger.Info("Mounting overlay from restored checkpoint", "imagePath", cm.overlayMgr.GetImagePath())

		// Mount the overlay
		if err := cm.overlayMgr.Mount(ctx); err != nil {
			// Log error but don't fail the restore
			cm.logger.Warn("Failed to mount overlay after restore", "error", err)
		}
	}

	// Apply quota asynchronously after restore
	go cm.applyActiveFsQuotaAsync()

	cm.logger.Info("Restore from checkpoint complete", "id", record.ID)
	return nil
}

// applyActiveFsQuotaAsync applies a 10TB quota to the active/fs directory asynchronously
func (cm *CheckpointManager) applyActiveFsQuotaAsync() {
	ctx := context.Background()

	// Construct metadata URL
	metaDB := filepath.Join(cm.baseDir, "metadata.db")
	metaURL := fmt.Sprintf("sqlite3://%s", metaDB)

	// Wait a moment for the mount to stabilize
	time.Sleep(2 * time.Second)

	cm.logger.Info("Applying 10TB quota to /active/fs directory")

	// Apply 10TB quota using juicefs quota command
	// 10TB = 10240 GiB
	quotaCmd := exec.CommandContext(ctx, "juicefs", "quota", "set", metaURL,
		"--path", "/active/fs",
		"--capacity", "10240")

	output, err := quotaCmd.CombinedOutput()
	if err != nil {
		// Check if quota already exists
		if strings.Contains(string(output), "already exists") {
			cm.logger.Info("Quota already exists for /active/fs directory")
		} else {
			cm.logger.Warn("Failed to apply quota to /active/fs", "error", err, "output", string(output))
		}
	} else {
		cm.logger.Info("Successfully applied 10TB quota to /active/fs directory")
		if len(output) > 0 {
			cm.logger.Debug("Quota info", "output", string(output))
		}
	}
}

// ListCheckpoints returns a list of all available checkpoints
// ... existing code ...
