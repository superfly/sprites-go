package overlay

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
)

// PrepFunc is a middleware-like function that prepares for a checkpoint/restore.
// It must return a resume function that undoes the preparation when called.
// The resume function must be safe to call exactly once.
type PrepFunc func(ctx context.Context) (resume func() error, err error)

// Chain returns a PrepFunc that runs the provided funcs in order, and resumes in reverse order.
func Chain(funcs ...PrepFunc) PrepFunc {
	return func(ctx context.Context) (func() error, error) {
		var resumes []func() error
		for _, f := range funcs {
			resume, err := f(ctx)
			if err != nil {
				// On error, resume everything already prepared in reverse order.
				for i := len(resumes) - 1; i >= 0; i-- {
					_ = resumes[i]()
				}
				return nil, err
			}
			if resume != nil {
				resumes = append(resumes, resume)
			}
		}
		// Compose reverse resume
		return func() error {
			var firstErr error
			for i := len(resumes) - 1; i >= 0; i-- {
				if err := resumes[i](); err != nil && firstErr == nil {
					firstErr = err
				}
			}
			return firstErr
		}, nil
	}
}

// NoopPrep returns a PrepFunc that does nothing and resumes with no-op.
func NoopPrep() PrepFunc {
	return func(ctx context.Context) (func() error, error) {
		return func() error { return nil }, nil
	}
}

// filesystemOps handles clone and rename operations on checkpoint paths.
type filesystemOps struct {
	baseDir     string
	copyCommand []string // e.g. ["juicefs", "clone"]
	logger      *slog.Logger
}

// newFilesystemOps creates filesystem ops with a configurable copy command.
// copyCommand should be the command and its args (e.g., ["juicefs", "clone"]).
func newFilesystemOps(baseDir string, copyCommand []string, logger *slog.Logger) *filesystemOps {
	return &filesystemOps{baseDir: baseDir, copyCommand: copyCommand, logger: logger}
}

func (o *filesystemOps) Clone(ctx context.Context, srcRel, dstRel string) error {
	src := filepath.Join(o.baseDir, srcRel)
	dst := filepath.Join(o.baseDir, dstRel)
	if len(o.copyCommand) == 0 {
		return fmt.Errorf("copy command not configured")
	}
	args := append(append([]string{}, o.copyCommand[1:]...), src, dst)
	cmd := exec.CommandContext(ctx, o.copyCommand[0], args...)
	if output, err := cmd.CombinedOutput(); err != nil {
		return fmt.Errorf("%s: %w, output: %s", strings.Join(o.copyCommand, " "), err, string(output))
	}
	return nil
}

func (o *filesystemOps) Rename(ctx context.Context, srcRel, dstRel string) error {
	src := filepath.Join(o.baseDir, srcRel)
	if dstRel == "" {
		return os.RemoveAll(src)
	}
	dst := filepath.Join(o.baseDir, dstRel)
	return os.Rename(src, dst)
}

// renameOrphanedCheckpoints scans the checkpoints directory and renames any
// checkpoint folders that are not tracked in the database.
func renameOrphanedCheckpoints(fsBaseDir string, dbCheckpoints []CheckpointRecord, logger *slog.Logger) error {
	checkpointsDir := filepath.Join(fsBaseDir, "checkpoints")

	// Create a map of known checkpoint paths from the database
	knownPaths := make(map[string]bool)
	for _, rec := range dbCheckpoints {
		knownPaths[rec.Path] = true
	}

	// Read all entries in the checkpoints directory
	entries, err := os.ReadDir(checkpointsDir)
	if err != nil {
		if os.IsNotExist(err) {
			// No checkpoints directory yet, nothing to clean up
			return nil
		}
		return fmt.Errorf("read checkpoints directory: %w", err)
	}

	// Check each entry
	for _, entry := range entries {
		if !entry.IsDir() {
			continue
		}

		name := entry.Name()
		// Skip already orphaned directories and in-progress directories
		if strings.HasSuffix(name, ".orphaned") || strings.HasSuffix(name, ".in-progress") {
			continue
		}

		// Construct the relative path as stored in DB
		checkpointPath := filepath.Join("checkpoints", name)

		// If this checkpoint is not in the database, mark it as orphaned
		if !knownPaths[checkpointPath] {
			oldPath := filepath.Join(checkpointsDir, name)
			newPath := filepath.Join(checkpointsDir, name+".orphaned")

			if logger != nil {
				logger.Info("Renaming orphaned checkpoint directory",
					"oldPath", checkpointPath,
					"newPath", filepath.Join("checkpoints", name+".orphaned"))
			}

			if err := os.Rename(oldPath, newPath); err != nil {
				return fmt.Errorf("rename orphaned checkpoint %s: %w", checkpointPath, err)
			}
		}
	}

	return nil
}

// Checkpoint creates a checkpoint of the current system state
func (m *Manager) Checkpoint(ctx context.Context) (*CheckpointRecord, error) {
	if m.checkpointDB == nil {
		return nil, fmt.Errorf("checkpoint manager not initialized")
	}

	var resume func() error
	var err error
	if m.checkpointPrepare != nil {
		resume, err = m.checkpointPrepare(ctx)
		if err != nil {
			return nil, fmt.Errorf("prepare for checkpoint failed: %w", err)
		}
		defer func() { _ = resume() }()
	}

	rec, err := m.checkpointDB.createCheckpoint(
		func(src, dst string) error { return m.checkpointFS.Clone(ctx, src, dst) },
		func(src, dst string) error { return m.checkpointFS.Rename(ctx, src, dst) },
	)
	if err != nil {
		return nil, err
	}

	// Notify callback if set
	if m.onCheckpointCreated != nil {
		if err := m.onCheckpointCreated(ctx); err != nil {
			// Log but don't fail the checkpoint
			fmt.Fprintf(os.Stderr, "checkpoint created callback failed: %v\n", err)
		}
	}

	return rec, nil
}

// ListCheckpoints returns all checkpoint records (excluding active), newest first.
func (m *Manager) ListCheckpoints() ([]CheckpointRecord, error) {
	if m.checkpointDB == nil {
		return nil, fmt.Errorf("checkpoint manager not initialized")
	}
	return m.checkpointDB.listAll()
}

// GetLatestCheckpoint returns the newest checkpoint record.
func (m *Manager) GetLatestCheckpoint() (*CheckpointRecord, error) {
	if m.checkpointDB == nil {
		return nil, fmt.Errorf("checkpoint manager not initialized")
	}
	return m.checkpointDB.getLatest()
}

// FindCheckpointByIdentifier resolves a checkpoint identifier (e.g., "checkpoints/vN", "vN", "N") to a record.
func (m *Manager) FindCheckpointByIdentifier(id string) (*CheckpointRecord, error) {
	if m.checkpointDB == nil {
		return nil, fmt.Errorf("checkpoint manager not initialized")
	}
	rec, _, err := m.resolveCheckpoint(id)
	return rec, err
}

// Restore restores the active state from the given checkpoint identifier.
// The identifier may be one of:
// - "checkpoints/vN"
// - "vN"
// - numeric string "N"
// - other path segments interpreted as under "checkpoints/"
func (m *Manager) Restore(ctx context.Context, checkpointID string) error {
	if m.checkpointDB == nil {
		return fmt.Errorf("checkpoint manager not initialized")
	}
	if checkpointID == "" {
		return fmt.Errorf("checkpoint ID is required")
	}
	var resume func() error
	var err error
	if m.restorePrepare != nil {
		resume, err = m.restorePrepare(ctx)
		if err != nil {
			return fmt.Errorf("prepare for restore failed: %w", err)
		}
		defer func() { _ = resume() }()
	}

	// Resolve the checkpoint record
	rec, path, err := m.resolveCheckpoint(checkpointID)
	if err != nil {
		return err
	}

	// Backup current active directory if present
	backupRel := fmt.Sprintf("checkpoints/pre-restore-v%d-%d", rec.ID, timeNow())
	// Best-effort backup: ignore error if active/ doesn't exist
	_ = m.checkpointFS.Rename(ctx, "active", backupRel)

	// Restore by cloning checkpoint to active/
	if err := m.checkpointFS.Clone(ctx, path, "active"); err != nil {
		return fmt.Errorf("restore clone failed: %w", err)
	}
	return nil
}

// timeNow exists for testability
var timeNow = func() int64 { return time.Now().Unix() }

// resolveCheckpoint turns an identifier into a DB record and its path string (relative, e.g. "checkpoints/v3").
func (m *Manager) resolveCheckpoint(id string) (*CheckpointRecord, string, error) {
	// Already absolute within checkpoints
	if strings.HasPrefix(id, "checkpoints/v") {
		rec, err := m.checkpointDB.findCheckpointByPath(id)
		if err != nil {
			return nil, "", fmt.Errorf("checkpoint not found: %w", err)
		}
		return rec, id, nil
	}
	if strings.HasPrefix(id, "v") {
		path := filepath.Join("checkpoints", id)
		rec, err := m.checkpointDB.findCheckpointByPath(path)
		if err != nil {
			return nil, "", fmt.Errorf("checkpoint not found: %w", err)
		}
		return rec, path, nil
	}
	if n, convErr := strconv.ParseInt(id, 10, 64); convErr == nil {
		rec, err := m.checkpointDB.getCheckpointByID(n)
		if err != nil {
			return nil, "", fmt.Errorf("checkpoint %d not found: %w", n, err)
		}
		return rec, rec.Path, nil
	}
	// Treat as path segment under checkpoints/
	path := filepath.Join("checkpoints", id)
	rec, err := m.checkpointDB.findCheckpointByPath(path)
	if err != nil {
		return nil, "", fmt.Errorf("checkpoint not found: %w", err)
	}
	return rec, path, nil
}

// CleanupOrphanedCheckpoints scans for and renames checkpoint directories not in the database
func (m *Manager) CleanupOrphanedCheckpoints() error {
	if m.checkpointDB == nil {
		return fmt.Errorf("checkpoint manager not initialized")
	}
	existingCheckpoints, err := m.checkpointDB.listAll()
	if err != nil {
		return fmt.Errorf("list existing checkpoints: %w", err)
	}
	return renameOrphanedCheckpoints(m.checkpointFS.baseDir, existingCheckpoints, m.logger)
}

// SetOnCheckpointCreated sets a callback to be called after a checkpoint is successfully created
func (m *Manager) SetOnCheckpointCreated(callback func(ctx context.Context) error) {
	m.onCheckpointCreated = callback
}

// prepareCheckpoint returns a wrapper around next that prepares Manager
// and defers unfreeze on successful preparation.
func prepareCheckpoint(om *Manager, next PrepFunc) PrepFunc {
	return func(ctx context.Context) (func() error, error) {
		if om != nil {
			if err := om.PrepareForCheckpoint(ctx); err != nil {
				return nil, fmt.Errorf("overlay prepare checkpoint: %w", err)
			}
		}

		nextResume, err := next(ctx)
		if err != nil {
			if om != nil {
				_ = om.UnfreezeAfterCheckpoint(ctx)
			}
			return nil, err
		}

		return func() error {
			var firstErr error
			if nextResume != nil {
				if e := nextResume(); e != nil {
					firstErr = e
				}
			}
			if om != nil {
				if e := om.UnfreezeAfterCheckpoint(ctx); e != nil && firstErr == nil {
					firstErr = e
				}
			}
			return firstErr
		}, nil
	}
}

// prepareRestore ensures overlay is unmounted before restore and remounted after.
// Also calls container shutdown/boot callbacks if set.
func prepareRestore(om *Manager, next PrepFunc) PrepFunc {
	return func(ctx context.Context) (func() error, error) {
		if om != nil {
			// Call container shutdown callback if set
			if om.restoreContainerPrep != nil {
				if err := om.restoreContainerPrep(ctx); err != nil {
					return nil, fmt.Errorf("container shutdown before restore: %w", err)
				}
			}

			// Best-effort sync/freeze/unfreeze to flush outstanding writes
			_ = om.PrepareForCheckpoint(ctx)
			_ = om.UnfreezeAfterCheckpoint(ctx)
			if err := om.Unmount(ctx); err != nil {
				return nil, fmt.Errorf("overlay unmount before restore: %w", err)
			}
		}

		nextResume, err := next(ctx)
		if err != nil {
			// Nothing to resume yet; overlay stays unmounted on error
			return nil, err
		}

		return func() error {
			var firstErr error
			if nextResume != nil {
				if e := nextResume(); e != nil {
					firstErr = e
				}
			}
			if om != nil {
				if e := om.Mount(ctx); e != nil && firstErr == nil {
					firstErr = e
				}

				// Call container boot callback if set
				if om.restoreContainerResume != nil {
					if e := om.restoreContainerResume(ctx); e != nil && firstErr == nil {
						firstErr = e
					}
				}
			}
			return firstErr
		}, nil
	}
}
