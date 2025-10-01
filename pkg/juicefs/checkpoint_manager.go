package juicefs

import (
	"context"
	"fmt"
	"log/slog"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"time"

	"github.com/superfly/sprite-env/pkg/checkpoint"
	"github.com/superfly/sprite-env/pkg/tap"
)

// CheckpointManager handles all checkpoint and restore operations for JuiceFS
type CheckpointManager struct {
	baseDir string
	db      *CheckpointDB
	logger  *slog.Logger
}

// NewCheckpointManager creates a new checkpoint manager
func NewCheckpointManager(baseDir string, ctx context.Context) *CheckpointManager {
	logger := tap.Logger(ctx)

	return &CheckpointManager{
		baseDir: baseDir,
		logger:  logger,
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

	// Create checkpoint using the database transaction
	// Determine clone command (allow override for tests)
	cmd, args := resolveCloneCommand()

	record, err := cm.db.CreateCheckpoint(
		// Clone function
		func(src, dst string) error {
			// Convert relative paths to absolute paths
			srcPath := filepath.Join(mountPath, src)
			dstPath := filepath.Join(mountPath, dst)

			cm.logger.Debug("Creating checkpoint", "src", src, "dst", dst)
			cloneCmd := exec.CommandContext(ctx, cmd, append(args, srcPath, dstPath)...)
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

	// If active directory exists, back it up with a unique name
	if _, err := os.Stat(activeDir); err == nil {
		ts := time.Now().UnixNano()
		baseName := fmt.Sprintf("pre-restore-v%d-%d", record.ID, ts)
		backupPath := filepath.Join(checkpointsDir, baseName)
		// Ensure uniqueness in case of extremely fast successive restores
		for i := 1; ; i++ {
			if _, statErr := os.Stat(backupPath); os.IsNotExist(statErr) {
				break
			}
			backupPath = filepath.Join(checkpointsDir, fmt.Sprintf("%s-%d", baseName, i))
		}

		cm.logger.Debug("Backing up current active directory", "backupPath", backupPath)
		if err := os.Rename(activeDir, backupPath); err != nil {
			return fmt.Errorf("failed to backup active directory: %w", err)
		}
		cm.logger.Debug("Backup completed")
	}

	// Clone checkpoint to active directory
	cm.logger.Debug("Restoring from checkpoint", "id", record.ID, "path", checkpointPath)
	// Determine clone command (allow override for tests)
	cmd, args := resolveCloneCommand()
	cloneCmd := exec.CommandContext(ctx, cmd, append(args, fullCheckpointPath, activeDir)...)
	if output, err := cloneCmd.CombinedOutput(); err != nil {
		return fmt.Errorf("failed to restore from checkpoint: %w, output: %s", err, string(output))
	}

	// Apply quota asynchronously after restore
	go cm.applyActiveFsQuotaAsync()

	cm.logger.Info("Restore from checkpoint complete", "id", record.ID)
	return nil
}

// applyActiveFsQuotaAsync applies a 10TB quota to the active/fs directory asynchronously
func (cm *CheckpointManager) applyActiveFsQuotaAsync() {
	// Use a context with a reasonable timeout to prevent hanging
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	// Construct metadata URL
	metaDB := filepath.Join(cm.baseDir, "metadata.db")
	metaURL := fmt.Sprintf("sqlite3://%s", metaDB)

	// Wait a moment for the mount to stabilize
	select {
	case <-time.After(2 * time.Second):
	case <-ctx.Done():
		cm.logger.Debug("Quota application cancelled due to timeout")
		return
	}

	cm.logger.Info("Applying 10TB quota to /active/fs directory")

	// Apply 10TB quota using juicefs quota command
	// 10TB = 10240 GiB
	quotaCmd := exec.CommandContext(ctx, "juicefs", "quota", "set", metaURL,
		"--path", "/active/fs",
		"--capacity", "10240")
	quotaCmd.Env = append(os.Environ(), "JUICEFS_LOG_FORMAT=json")

	output, err := quotaCmd.CombinedOutput()
	if err != nil {
		// Check if context was cancelled
		if ctx.Err() != nil {
			cm.logger.Debug("Quota application cancelled due to timeout")
			return
		}
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

// PrepareCheckpoint wraps a checkpoint.PrepFunc (shim for legacy tests)
func PrepareCheckpoint(inner checkpoint.PrepFunc) checkpoint.PrepFunc { return inner }

// PrepareRestore wraps a checkpoint.PrepFunc (shim for legacy tests)
func PrepareRestore(inner checkpoint.PrepFunc) checkpoint.PrepFunc { return inner }
