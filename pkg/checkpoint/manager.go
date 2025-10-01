package checkpoint

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

// Manager coordinates checkpoint and restore using a DB and filesystem ops.
type Manager struct {
	db        *SQLiteDB
	fs        *filesystemOps
	prepareCP PrepFunc
	prepareRS PrepFunc
}

// Record mirrors the DB record used by checkpointing.
type Record struct {
	ID        int64
	Path      string
	CreatedAt time.Time
}

// NewManager constructs a Manager with the given configuration.
// dbPath: path to SQLite checkpoint database
// fsBaseDir: base directory for checkpoint filesystem operations
// copyCommand: command to use for copying (e.g., ["juicefs", "clone"])
// prepareCheckpoint, prepareRestore: optional preparation functions
func NewManager(dbPath string, fsBaseDir string, copyCommand []string, logger *slog.Logger, prepareCheckpoint PrepFunc, prepareRestore PrepFunc) (*Manager, error) {
	// Create DB
	db, err := NewSQLiteDB(SQLiteConfig{DBPath: dbPath, Logger: logger})
	if err != nil {
		return nil, fmt.Errorf("init checkpoint db: %w", err)
	}

	// Create filesystem ops
	fs := newFilesystemOps(fsBaseDir, copyCommand, logger)

	// Query existing checkpoints before initialization
	existingCheckpoints, err := db.ListAll()
	if err != nil {
		db.Close()
		return nil, fmt.Errorf("list existing checkpoints: %w", err)
	}

	if logger != nil {
		logger.Info("Checkpoint manager starting",
			"dbPath", dbPath,
			"fsBaseDir", fsBaseDir,
			"copyCommand", strings.Join(copyCommand, " "),
			"existingCheckpoints", len(existingCheckpoints))
	}

	// Create v0 directory if it doesn't exist
	v0Path := filepath.Join(fsBaseDir, "checkpoints", "v0")
	if _, err := os.Stat(v0Path); os.IsNotExist(err) {
		if err := os.MkdirAll(v0Path, 0755); err != nil {
			db.Close()
			return nil, fmt.Errorf("create v0 checkpoint directory: %w", err)
		}
		if logger != nil {
			logger.Info("Created empty v0 checkpoint directory", "path", v0Path)
		}
	}

	if logger != nil {
		logger.Info("Checkpoint manager configured",
			"dbPath", dbPath,
			"fsBaseDir", fsBaseDir,
			"copyCommand", strings.Join(copyCommand, " "))
	}

	return &Manager{db: db, fs: fs, prepareCP: prepareCheckpoint, prepareRS: prepareRestore}, nil
}

// Close closes the underlying database connection.
func (m *Manager) Close() error {
	if m.db != nil {
		return m.db.Close()
	}
	return nil
}

// Checkpoint performs a checkpoint, running preparation chain if provided.
func (m *Manager) Checkpoint(ctx context.Context) (*Record, error) {
	var resume func() error
	var err error
	if m.prepareCP != nil {
		resume, err = m.prepareCP(ctx)
		if err != nil {
			return nil, fmt.Errorf("prepare for checkpoint failed: %w", err)
		}
		defer func() { _ = resume() }()
	}

	rec, err := m.db.CreateCheckpoint(
		func(src, dst string) error { return m.fs.Clone(ctx, src, dst) },
		func(src, dst string) error { return m.fs.Rename(ctx, src, dst) },
	)
	if err != nil {
		return nil, err
	}
	return rec, nil
}

// ListAll returns all checkpoint records (excluding active), newest first.
func (m *Manager) ListAll() ([]Record, error) {
	return m.db.ListAll()
}

// GetLatest returns the newest checkpoint record.
func (m *Manager) GetLatest() (*Record, error) {
	return m.db.GetLatest()
}

// FindByIdentifier resolves a checkpoint identifier (e.g., "checkpoints/vN", "vN", "N") to a record.
func (m *Manager) FindByIdentifier(id string) (*Record, error) {
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
	if checkpointID == "" {
		return fmt.Errorf("checkpoint ID is required")
	}
	var resume func() error
	var err error
	if m.prepareRS != nil {
		resume, err = m.prepareRS(ctx)
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
	_ = m.fs.Rename(ctx, "active", backupRel)

	// Restore by cloning checkpoint to active/
	if err := m.fs.Clone(ctx, path, "active"); err != nil {
		return fmt.Errorf("restore clone failed: %w", err)
	}
	return nil
}

// timeNow exists for testability
var timeNow = func() int64 { return time.Now().Unix() }

// resolveCheckpoint turns an identifier into a DB record and its path string (relative, e.g. "checkpoints/v3").
func (m *Manager) resolveCheckpoint(id string) (*Record, string, error) {
	// Already absolute within checkpoints
	if strings.HasPrefix(id, "checkpoints/v") {
		rec, err := m.db.FindCheckpointByPath(id)
		if err != nil {
			return nil, "", fmt.Errorf("checkpoint not found: %w", err)
		}
		return rec, id, nil
	}
	if strings.HasPrefix(id, "v") {
		path := filepath.Join("checkpoints", id)
		rec, err := m.db.FindCheckpointByPath(path)
		if err != nil {
			return nil, "", fmt.Errorf("checkpoint not found: %w", err)
		}
		return rec, path, nil
	}
	if n, convErr := strconv.ParseInt(id, 10, 64); convErr == nil {
		rec, err := m.db.GetCheckpointByID(n)
		if err != nil {
			return nil, "", fmt.Errorf("checkpoint %d not found: %w", n, err)
		}
		return rec, rec.Path, nil
	}
	// Treat as path segment under checkpoints/
	path := filepath.Join("checkpoints", id)
	rec, err := m.db.FindCheckpointByPath(path)
	if err != nil {
		return nil, "", fmt.Errorf("checkpoint not found: %w", err)
	}
	return rec, path, nil
}
