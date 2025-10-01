package juicefs

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"time"
)

// CheckpointInfo represents a checkpoint returned by legacy JuiceFS APIs used in tests.
type CheckpointInfo struct {
	ID         string
	CreateTime time.Time
}

// ListCheckpoints returns checkpoints known to the embedded CheckpointDB, newest first.
func (j *JuiceFS) ListCheckpoints(ctx context.Context) ([]CheckpointInfo, error) {
	if j.checkpointDB == nil {
		return []CheckpointInfo{}, nil
	}
	records, err := j.checkpointDB.db.Query(`SELECT id, path, created_at FROM sprite_checkpoints ORDER BY id DESC`)
	if err != nil {
		return nil, fmt.Errorf("failed to list checkpoints: %w", err)
	}
	defer records.Close()

	var result []CheckpointInfo
	for records.Next() {
		var id int64
		var path string
		var created time.Time
		if err := records.Scan(&id, &path, &created); err != nil {
			return nil, fmt.Errorf("scan: %w", err)
		}
		// Only include real checkpoints under checkpoints/
		if strings.HasPrefix(path, "checkpoints/") {
			base := filepath.Base(path)
			result = append(result, CheckpointInfo{ID: base, CreateTime: created})
		}
	}
	return result, nil
}

// GetCheckpoint returns information about a checkpoint by identifier.
// Accepts identifiers like "v3", "checkpoints/v3", or "active".
func (j *JuiceFS) GetCheckpoint(ctx context.Context, checkpointID string) (*CheckpointInfo, error) {
	if checkpointID == "" {
		return nil, fmt.Errorf("checkpoint ID is required")
	}
	if j.checkpointDB == nil {
		return nil, fmt.Errorf("checkpoint database not initialized")
	}
	// Resolve identifier
	var path string
	if checkpointID == "active" {
		// Active version is latest ID - 1. We approximate by reading two latest rows.
		rows, err := j.checkpointDB.db.Query(`SELECT id, path, created_at FROM sprite_checkpoints ORDER BY id DESC LIMIT 2`)
		if err != nil {
			return nil, fmt.Errorf("query active: %w", err)
		}
		defer rows.Close()
		var infos []struct {
			id      int64
			path    string
			created time.Time
		}
		for rows.Next() {
			var r struct {
				id      int64
				path    string
				created time.Time
			}
			if err := rows.Scan(&r.id, &r.path, &r.created); err != nil {
				return nil, err
			}
			infos = append(infos, r)
		}
		// Expect at least two rows initially (v0 and active)
		if len(infos) == 0 {
			return nil, fmt.Errorf("no checkpoints in database")
		}
		// Active corresponds to previous version name "v{latestID-1}"
		latestID := infos[0].id
		activeID := latestID - 1
		return &CheckpointInfo{ID: fmt.Sprintf("v%d", activeID), CreateTime: infos[0].created}, nil
	}
	if strings.HasPrefix(checkpointID, "checkpoints/") {
		path = checkpointID
	} else if strings.HasPrefix(checkpointID, "v") {
		path = filepath.Join("checkpoints", checkpointID)
	} else {
		// Try as literal under checkpoints
		path = filepath.Join("checkpoints", checkpointID)
	}

	rec, err := j.checkpointDB.FindCheckpointByPath(path)
	if err != nil {
		return nil, err
	}
	base := filepath.Base(rec.Path)
	return &CheckpointInfo{ID: base, CreateTime: rec.CreatedAt}, nil
}

// ListCheckpointsWithActive returns a list prefixed with the current working state.
func (j *JuiceFS) ListCheckpointsWithActive(ctx context.Context) ([]CheckpointInfo, error) {
	// Start with Current entry
	out := []CheckpointInfo{{ID: "Current", CreateTime: time.Now()}}
	rest, err := j.ListCheckpoints(ctx)
	if err != nil {
		return nil, err
	}
	out = append(out, rest...)
	return out, nil
}

// Checkpoint triggers a checkpoint via the embedded DB transactional API.
func (j *JuiceFS) Checkpoint(ctx context.Context, _ string) error {
	if j.checkpointDB == nil {
		return fmt.Errorf("checkpoint database not initialized")
	}
	// Use `juicefs clone` by default; allow override via JUICEFS_CLONE_CMD during tests by delegating to checkpoint manager logic
	// Here we use the DB's CreateCheckpoint with real filesystem cloning via juicefs.
	mountPath := filepath.Join(j.config.BaseDir, "data")
	_, err := j.checkpointDB.CreateCheckpoint(
		func(src, dst string) error {
			// Build full paths and run clone
			srcPath := filepath.Join(mountPath, src)
			dstPath := filepath.Join(mountPath, dst)
			cmd, args := resolveCloneCommand()
			return runClone(ctx, cmd, append(args, srcPath, dstPath)...)
		},
		func(src, dst string) error {
			srcPath := filepath.Join(mountPath, src)
			if dst == "" {
				return os.RemoveAll(srcPath)
			}
			dstPath := filepath.Join(mountPath, dst)
			return os.Rename(srcPath, dstPath)
		},
	)
	return err
}

// Restore restores the active state from the given checkpoint identifier.
func (j *JuiceFS) Restore(ctx context.Context, checkpointID string) error {
	if checkpointID == "" {
		return fmt.Errorf("checkpoint ID is required")
	}
	if j.checkpointDB == nil {
		return fmt.Errorf("checkpoint database not initialized")
	}
	// Reuse CheckpointManager semantics to resolve identifier
	cm := &CheckpointManager{baseDir: j.config.BaseDir, db: j.checkpointDB, logger: j.logger}
	return cm.Restore(ctx, checkpointID)
}

// Helpers used by Checkpoint
func resolveCloneCommand() (string, []string) {
	cmd := "juicefs"
	args := []string{"clone"}
	if override := strings.TrimSpace(os.Getenv("JUICEFS_CLONE_CMD")); override != "" {
		parts := strings.Fields(override)
		if len(parts) > 0 {
			cmd = parts[0]
			args = parts[1:]
		}
	}
	return cmd, args
}

func runClone(ctx context.Context, cmd string, args ...string) error {
	command := exec.CommandContext(ctx, cmd, args...)
	if output, err := command.CombinedOutput(); err != nil {
		return fmt.Errorf("%s %s: %w, output: %s", cmd, strings.Join(args, " "), err, string(output))
	}
	return nil
}
