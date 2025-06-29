package juicefs

import (
	"context"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

func TestListCheckpoints(t *testing.T) {
	tmpDir := t.TempDir()

	config := Config{
		BaseDir:           tmpDir,
		S3AccessKey:       "test",
		S3SecretAccessKey: "test",
		S3EndpointURL:     "http://localhost:9000",
		S3Bucket:          "test",
	}

	jfs, err := New(config)
	if err != nil {
		t.Fatalf("Failed to create JuiceFS: %v", err)
	}

	// Initialize checkpoint database for testing
	mountPath := filepath.Join(tmpDir, "data")
	if err := os.MkdirAll(mountPath, 0755); err != nil {
		t.Fatalf("Failed to create mount path: %v", err)
	}

	db, err := NewCheckpointDB(CheckpointDBConfig{
		BaseDir: mountPath,
	})
	if err != nil {
		t.Fatalf("Failed to create checkpoint database: %v", err)
	}
	jfs.checkpointDB = db
	defer db.Close()

	ctx := context.Background()

	// Test with no checkpoints directory
	checkpoints, err := jfs.ListCheckpoints(ctx)
	if err != nil {
		t.Fatalf("Failed to list checkpoints: %v", err)
	}
	// Now we start with a v0 checkpoint, but ListCheckpoints only returns checkpoints with "checkpoints/" prefix
	// The initial v0 is at "checkpoints/v0" so we should have 1
	if len(checkpoints) != 1 {
		t.Errorf("Expected 1 checkpoint (v0), got %d", len(checkpoints))
	}

	// Create checkpoints directory and some test checkpoints
	checkpointsDir := filepath.Join(mountPath, "checkpoints")
	if err := os.MkdirAll(checkpointsDir, 0755); err != nil {
		t.Fatalf("Failed to create checkpoints directory: %v", err)
	}

	// Create test checkpoints using the SQLite database
	// Insert test checkpoints directly into the database
	// We start with v0 already existing, so create v1, v2, v3
	for i := 1; i <= 3; i++ {
		checkpointPath := fmt.Sprintf("checkpoints/v%d", i)
		_, err := db.db.Exec("INSERT INTO sprite_checkpoints (path, parent_id) VALUES (?, ?)", checkpointPath, nil)
		if err != nil {
			t.Fatalf("Failed to insert checkpoint v%d: %v", i, err)
		}
		time.Sleep(10 * time.Millisecond) // Ensure different timestamps
	}

	// Create symlinks that should be skipped
	if err := os.Symlink("v2", filepath.Join(checkpointsDir, ".latest_version")); err != nil {
		t.Logf("Failed to create .latest_version symlink: %v", err)
	}
	if err := os.Symlink("v2/.version", filepath.Join(checkpointsDir, ".latest")); err != nil {
		t.Logf("Failed to create .latest symlink: %v", err)
	}

	// Test listing checkpoints
	checkpoints, err = jfs.ListCheckpoints(ctx)
	if err != nil {
		t.Fatalf("Failed to list checkpoints: %v", err)
	}

	// Should have 4 checkpoints (v0 + v1, v2, v3) (symlinks should be skipped)
	if len(checkpoints) != 4 {
		t.Errorf("Expected 4 checkpoints, got %d", len(checkpoints))
	}

	// Verify checkpoint details
	foundV0 := false
	foundV1 := false
	foundV2 := false
	foundV3 := false
	for _, cp := range checkpoints {
		if cp.ID == "v0" {
			foundV0 = true
		} else if cp.ID == "v1" {
			foundV1 = true
		} else if cp.ID == "v2" {
			foundV2 = true
		} else if cp.ID == "v3" {
			foundV3 = true
		}
	}

	if !foundV0 {
		t.Error("v0 not found in list")
	}
	if !foundV1 {
		t.Error("v1 not found in list")
	}
	if !foundV2 {
		t.Error("v2 not found in list")
	}
	if !foundV3 {
		t.Error("v3 not found in list")
	}
}

func TestGetCheckpoint(t *testing.T) {
	tmpDir := t.TempDir()

	config := Config{
		BaseDir:           tmpDir,
		S3AccessKey:       "test",
		S3SecretAccessKey: "test",
		S3EndpointURL:     "http://localhost:9000",
		S3Bucket:          "test",
	}

	jfs, err := New(config)
	if err != nil {
		t.Fatalf("Failed to create JuiceFS: %v", err)
	}

	// Initialize checkpoint database for testing
	mountPath := filepath.Join(tmpDir, "data")
	if err := os.MkdirAll(mountPath, 0755); err != nil {
		t.Fatalf("Failed to create mount path: %v", err)
	}

	db, err := NewCheckpointDB(CheckpointDBConfig{
		BaseDir: mountPath,
	})
	if err != nil {
		t.Fatalf("Failed to create checkpoint database: %v", err)
	}
	jfs.checkpointDB = db
	defer db.Close()

	ctx := context.Background()

	// Test with non-existent checkpoint
	_, err = jfs.GetCheckpoint(ctx, "non-existent")
	if err == nil {
		t.Error("Expected error for non-existent checkpoint")
	}

	// Create a test checkpoint in the database
	_, err = db.db.Exec("INSERT INTO sprite_checkpoints (path, parent_id) VALUES (?, ?)", "checkpoints/v3", nil)
	if err != nil {
		t.Fatalf("Failed to insert checkpoint v3: %v", err)
	}

	// Note: History files are no longer used

	// Test getting checkpoint
	checkpoint, err := jfs.GetCheckpoint(ctx, "v3")
	if err != nil {
		t.Fatalf("Failed to get checkpoint: %v", err)
	}

	if checkpoint.ID != "v3" {
		t.Errorf("Expected ID 'v3', got %s", checkpoint.ID)
	}

	// Note: History checking removed - history files are no longer used

	// Test empty checkpoint ID
	_, err = jfs.GetCheckpoint(ctx, "")
	if err == nil {
		t.Error("Expected error for empty checkpoint ID")
	}
}

func TestListCheckpointsWithActive(t *testing.T) {
	tmpDir := t.TempDir()

	config := Config{
		BaseDir:           tmpDir,
		S3AccessKey:       "test",
		S3SecretAccessKey: "test",
		S3EndpointURL:     "http://localhost:9000",
		S3Bucket:          "test",
	}

	jfs, err := New(config)
	if err != nil {
		t.Fatalf("Failed to create JuiceFS: %v", err)
	}

	// Initialize checkpoint database for testing
	mountPath := filepath.Join(tmpDir, "data")
	if err := os.MkdirAll(mountPath, 0755); err != nil {
		t.Fatalf("Failed to create mount path: %v", err)
	}

	db, err := NewCheckpointDB(CheckpointDBConfig{
		BaseDir: mountPath,
	})
	if err != nil {
		t.Fatalf("Failed to create checkpoint database: %v", err)
	}
	jfs.checkpointDB = db
	defer db.Close()

	ctx := context.Background()

	// Create necessary directories
	activeDir := filepath.Join(mountPath, "active")
	checkpointsDir := filepath.Join(mountPath, "checkpoints")

	if err := os.MkdirAll(activeDir, 0755); err != nil {
		t.Fatalf("Failed to create active directory: %v", err)
	}
	if err := os.MkdirAll(checkpointsDir, 0755); err != nil {
		t.Fatalf("Failed to create checkpoints directory: %v", err)
	}

	// Note: Version files are no longer used in SQLite system

	// Create some test checkpoints in the database
	// Insert 3 additional checkpoints - the initial v0 already exists
	// Create v1, v2, v3
	for i := 1; i <= 3; i++ {
		checkpointPath := fmt.Sprintf("checkpoints/v%d", i)
		_, err := db.db.Exec("INSERT INTO sprite_checkpoints (path, parent_id) VALUES (?, ?)", checkpointPath, nil)
		if err != nil {
			t.Fatalf("Failed to insert checkpoint v%d: %v", i, err)
		}
		time.Sleep(10 * time.Millisecond) // Ensure different timestamps
	}

	// Test ListCheckpointsWithActive
	checkpoints, err := jfs.ListCheckpointsWithActive(ctx)
	if err != nil {
		t.Fatalf("Failed to list checkpoints with active: %v", err)
	}

	// Should have 5 checkpoints (4 checkpoints: v0, v1, v2, v3 + 1 active)
	if len(checkpoints) != 5 {
		t.Errorf("Expected 5 checkpoints, got %d", len(checkpoints))
	}

	// First should be the active version (latest checkpoint ID - 1)
	if !strings.HasSuffix(checkpoints[0].ID, " (active)") {
		t.Errorf("Expected first checkpoint to end with ' (active)', got %s", checkpoints[0].ID)
	}

	// Verify we have the expected number of checkpoints (4 regular + 1 active)
	if len(checkpoints) != 5 {
		return // Already failed above
	}

	// The remaining should be the actual checkpoints v3, v2, v1, v0 in reverse order
	expectedCheckpoints := []string{"v3", "v2", "v1", "v0"}
	for i, expected := range expectedCheckpoints {
		actualIndex := i + 1 // Skip the active checkpoint at index 0
		if actualIndex >= len(checkpoints) {
			t.Errorf("Missing checkpoint at index %d, expected %s", actualIndex, expected)
			continue
		}
		if checkpoints[actualIndex].ID != expected {
			t.Errorf("At index %d: expected %s, got %s", actualIndex, expected, checkpoints[actualIndex].ID)
		}
	}
}

func TestGetCheckpointActive(t *testing.T) {
	tmpDir := t.TempDir()

	config := Config{
		BaseDir:           tmpDir,
		S3AccessKey:       "test",
		S3SecretAccessKey: "test",
		S3EndpointURL:     "http://localhost:9000",
		S3Bucket:          "test",
	}

	jfs, err := New(config)
	if err != nil {
		t.Fatalf("Failed to create JuiceFS: %v", err)
	}

	// Initialize checkpoint database for testing
	mountPath := filepath.Join(tmpDir, "data")
	if err := os.MkdirAll(mountPath, 0755); err != nil {
		t.Fatalf("Failed to create mount path: %v", err)
	}

	db, err := NewCheckpointDB(CheckpointDBConfig{
		BaseDir: mountPath,
	})
	if err != nil {
		t.Fatalf("Failed to create checkpoint database: %v", err)
	}
	jfs.checkpointDB = db
	defer db.Close()

	ctx := context.Background()

	// Create necessary directories
	activeDir := filepath.Join(mountPath, "active")

	if err := os.MkdirAll(activeDir, 0755); err != nil {
		t.Fatalf("Failed to create active directory: %v", err)
	}

	// Note: Version files are no longer used in SQLite system
	// The initial database starts with ID=1 for v0 and ID=2 for active, so active version is v1

	// Test getting active checkpoint
	checkpoint, err := jfs.GetCheckpoint(ctx, "active")
	if err != nil {
		t.Fatalf("Failed to get active checkpoint: %v", err)
	}

	// In the SQLite system, the active version is the latest checkpoint ID - 1
	// Since we start with ID=2 for active, the active version is v1
	if checkpoint.ID != "v1" {
		t.Errorf("Expected ID 'v1', got %s", checkpoint.ID)
	}

	// Note: History checking removed - history files are no longer used
}
