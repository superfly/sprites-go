//go:build linux

package overlay

import (
	"context"
	"os"
	"path/filepath"
	"testing"
)

// TestDeleteCheckpointUnmountsAndRemoves verifies that deleting a checkpoint unmounts it and removes data
func TestDeleteCheckpointUnmountsAndRemoves(t *testing.T) {
	ctx := context.Background()
	baseDir := t.TempDir()

	// Set up manager
	cfg := Config{
		BaseDir:   baseDir,
		ImageSize: "100M",
	}
	m := New(cfg)

	// Initialize checkpoint DB and FS
	dbDir := filepath.Join(baseDir, "checkpoints")
	if err := os.MkdirAll(dbDir, 0755); err != nil {
		t.Fatal(err)
	}
	dbPath := filepath.Join(dbDir, "checkpoints.db")
	if err := m.InitializeCheckpointManager(ctx, dbPath); err != nil {
		t.Fatalf("init checkpoint manager: %v", err)
	}

	// Create a fake checkpoint directory to simulate a mountable checkpoint
	cpName := "v123"
	cpDir := filepath.Join(m.juicefsBasePath, "checkpoints", cpName)
	if err := os.MkdirAll(cpDir, 0755); err != nil {
		t.Fatal(err)
	}
	// Create a fake image file so doMountSingleCheckpoint would mount in real flow
	os.WriteFile(filepath.Join(cpDir, "root-upper.img"), []byte("fake"), 0644)

	// Manually record the checkpoint in DB so resolve works
	if _, err := m.checkpointDB.db.Exec("INSERT INTO sprite_checkpoints (path, parent_id) VALUES (?, NULL)", filepath.Join("checkpoints", cpName)); err != nil {
		t.Fatalf("seed checkpoint: %v", err)
	}

	// Simulate it being mounted by adding to maps
	m.checkpointMounts[cpName] = filepath.Join(m.checkpointMountPath, cpName)
	m.checkpointLoopDevices[cpName] = "/dev/loopX"

	// Delete the checkpoint
	if err := m.DeleteCheckpoint(ctx, cpName); err != nil {
		t.Fatalf("delete checkpoint: %v", err)
	}

	// Assert it's no longer tracked as mounted
	if m.isCheckpointMounted(cpName) {
		t.Fatalf("expected checkpoint %s to be unmounted", cpName)
	}
	if _, ok := m.checkpointLoopDevices[cpName]; ok {
		t.Fatalf("expected loop device mapping to be removed for %s", cpName)
	}

	// Assert the directory is removed
	if _, err := os.Stat(cpDir); !os.IsNotExist(err) {
		t.Fatalf("expected checkpoint directory removed, stat err=%v", err)
	}
}
