package juicefs

import (
	"context"
	"os"
	"path/filepath"
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

	ctx := context.Background()

	// Test with no checkpoints directory
	checkpoints, err := jfs.ListCheckpoints(ctx)
	if err != nil {
		t.Fatalf("Failed to list checkpoints: %v", err)
	}
	if len(checkpoints) != 0 {
		t.Errorf("Expected 0 checkpoints, got %d", len(checkpoints))
	}

	// Create checkpoints directory and some test checkpoints
	mountPath := filepath.Join(tmpDir, "data")
	checkpointsDir := filepath.Join(mountPath, "checkpoints")
	if err := os.MkdirAll(checkpointsDir, 0755); err != nil {
		t.Fatalf("Failed to create checkpoints directory: %v", err)
	}

	// Create test checkpoint directories
	testCheckpoints := []string{
		"v0",
		"v1",
		"v2",
	}

	for _, id := range testCheckpoints {
		cpDir := filepath.Join(checkpointsDir, id)
		if err := os.MkdirAll(cpDir, 0755); err != nil {
			t.Fatalf("Failed to create checkpoint directory %s: %v", id, err)
		}

		// Touch the directory to set modification time
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

	// Should have 3 checkpoints (symlinks should be skipped)
	if len(checkpoints) != 3 {
		t.Errorf("Expected 3 checkpoints, got %d", len(checkpoints))
	}

	// Verify checkpoint details
	foundV0 := false
	foundV1 := false
	foundV2 := false
	for _, cp := range checkpoints {
		if cp.ID == "v0" {
			foundV0 = true
		} else if cp.ID == "v1" {
			foundV1 = true
		} else if cp.ID == "v2" {
			foundV2 = true
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

	ctx := context.Background()

	// Test with non-existent checkpoint
	_, err = jfs.GetCheckpoint(ctx, "non-existent")
	if err == nil {
		t.Error("Expected error for non-existent checkpoint")
	}

	// Create a test checkpoint
	mountPath := filepath.Join(tmpDir, "data")
	checkpointsDir := filepath.Join(mountPath, "checkpoints")
	cpDir := filepath.Join(checkpointsDir, "v3")
	if err := os.MkdirAll(cpDir, 0755); err != nil {
		t.Fatalf("Failed to create checkpoint directory: %v", err)
	}

	// Add history file
	historyFile := filepath.Join(cpDir, ".history")
	historyContent := "to=v0;time=2024-01-01T10:00:00Z\nto=v1;time=2024-01-01T11:00:00Z\n"
	if err := os.WriteFile(historyFile, []byte(historyContent), 0644); err != nil {
		t.Fatalf("Failed to write history file: %v", err)
	}

	// Test getting checkpoint
	checkpoint, err := jfs.GetCheckpoint(ctx, "v3")
	if err != nil {
		t.Fatalf("Failed to get checkpoint: %v", err)
	}

	if checkpoint.ID != "v3" {
		t.Errorf("Expected ID 'v3', got %s", checkpoint.ID)
	}

	// Check history
	if len(checkpoint.History) != 2 {
		t.Errorf("Expected 2 history entries, got %d", len(checkpoint.History))
	} else {
		if checkpoint.History[0] != "to=v0;time=2024-01-01T10:00:00Z" {
			t.Errorf("Unexpected history[0]: %s", checkpoint.History[0])
		}
		if checkpoint.History[1] != "to=v1;time=2024-01-01T11:00:00Z" {
			t.Errorf("Unexpected history[1]: %s", checkpoint.History[1])
		}
	}

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

	ctx := context.Background()

	// Create necessary directories
	mountPath := filepath.Join(tmpDir, "data")
	activeDir := filepath.Join(mountPath, "active")
	checkpointsDir := filepath.Join(mountPath, "checkpoints")

	if err := os.MkdirAll(activeDir, 0755); err != nil {
		t.Fatalf("Failed to create active directory: %v", err)
	}
	if err := os.MkdirAll(checkpointsDir, 0755); err != nil {
		t.Fatalf("Failed to create checkpoints directory: %v", err)
	}

	// Create a version file
	versionFile := filepath.Join(activeDir, ".version")
	if err := os.WriteFile(versionFile, []byte("v3\n"), 0644); err != nil {
		t.Fatalf("Failed to write version file: %v", err)
	}

	// Create a history file
	historyFile := filepath.Join(activeDir, ".history")
	historyContent := "to=v0;time=2024-01-01T10:00:00Z\nto=v1;time=2024-01-01T11:00:00Z\n"
	if err := os.WriteFile(historyFile, []byte(historyContent), 0644); err != nil {
		t.Fatalf("Failed to write history file: %v", err)
	}

	// Create some test checkpoints
	testCheckpoints := []string{"v0", "v1", "v2"}
	for i, id := range testCheckpoints {
		cpDir := filepath.Join(checkpointsDir, id)
		if err := os.MkdirAll(cpDir, 0755); err != nil {
			t.Fatalf("Failed to create checkpoint directory %s: %v", id, err)
		}
		// Sleep to ensure different timestamps
		time.Sleep(10 * time.Millisecond * time.Duration(i+1))
	}

	// Test ListCheckpointsWithActive
	checkpoints, err := jfs.ListCheckpointsWithActive(ctx)
	if err != nil {
		t.Fatalf("Failed to list checkpoints with active: %v", err)
	}

	// Should have 4 checkpoints (3 + active)
	if len(checkpoints) != 4 {
		t.Errorf("Expected 4 checkpoints, got %d", len(checkpoints))
	}

	// First should be the active version
	if checkpoints[0].ID != "v3 (active)" {
		t.Errorf("Expected first checkpoint to be 'v3 (active)', got %s", checkpoints[0].ID)
	}

	// Next should be v2, v1, v0 in reverse order
	expectedOrder := []string{"v3 (active)", "v2", "v1", "v0"}
	for i, expected := range expectedOrder {
		if i >= len(checkpoints) {
			t.Errorf("Missing checkpoint at index %d, expected %s", i, expected)
			continue
		}
		if checkpoints[i].ID != expected {
			t.Errorf("At index %d: expected %s, got %s", i, expected, checkpoints[i].ID)
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

	ctx := context.Background()

	// Create necessary directories
	mountPath := filepath.Join(tmpDir, "data")
	activeDir := filepath.Join(mountPath, "active")

	if err := os.MkdirAll(activeDir, 0755); err != nil {
		t.Fatalf("Failed to create active directory: %v", err)
	}

	// Create a version file
	versionFile := filepath.Join(activeDir, ".version")
	if err := os.WriteFile(versionFile, []byte("v5\n"), 0644); err != nil {
		t.Fatalf("Failed to write version file: %v", err)
	}

	// Create a history file
	historyFile := filepath.Join(activeDir, ".history")
	historyContent := "to=v0;time=2024-01-01T10:00:00Z\nto=v2;time=2024-01-01T11:00:00Z\n"
	if err := os.WriteFile(historyFile, []byte(historyContent), 0644); err != nil {
		t.Fatalf("Failed to write history file: %v", err)
	}

	// Test getting active checkpoint
	checkpoint, err := jfs.GetCheckpoint(ctx, "active")
	if err != nil {
		t.Fatalf("Failed to get active checkpoint: %v", err)
	}

	if checkpoint.ID != "v5" {
		t.Errorf("Expected ID 'v5', got %s", checkpoint.ID)
	}

	// Check history
	if len(checkpoint.History) != 2 {
		t.Errorf("Expected 2 history entries, got %d", len(checkpoint.History))
	} else {
		if checkpoint.History[0] != "to=v0;time=2024-01-01T10:00:00Z" {
			t.Errorf("Unexpected history[0]: %s", checkpoint.History[0])
		}
		if checkpoint.History[1] != "to=v2;time=2024-01-01T11:00:00Z" {
			t.Errorf("Unexpected history[1]: %s", checkpoint.History[1])
		}
	}
}
