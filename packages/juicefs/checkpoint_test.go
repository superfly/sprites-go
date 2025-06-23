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
	testCheckpoints := []struct {
		id       string
		sourceID string
	}{
		{"checkpoint-1", ""},
		{"checkpoint-2", "checkpoint-1"},
		{"pre-restore-test-123", ""}, // Should be skipped
	}

	for _, tc := range testCheckpoints {
		cpDir := filepath.Join(checkpointsDir, tc.id)
		if err := os.MkdirAll(cpDir, 0755); err != nil {
			t.Fatalf("Failed to create checkpoint directory %s: %v", tc.id, err)
		}

		// Add source file if specified
		if tc.sourceID != "" {
			sourceFile := filepath.Join(cpDir, ".source")
			if err := os.WriteFile(sourceFile, []byte(tc.sourceID), 0644); err != nil {
				t.Fatalf("Failed to write source file: %v", err)
			}
		}

		// Touch the directory to set modification time
		time.Sleep(10 * time.Millisecond) // Ensure different timestamps
	}

	// Test listing checkpoints
	checkpoints, err = jfs.ListCheckpoints(ctx)
	if err != nil {
		t.Fatalf("Failed to list checkpoints: %v", err)
	}

	// Should have 2 checkpoints (pre-restore should be skipped)
	if len(checkpoints) != 2 {
		t.Errorf("Expected 2 checkpoints, got %d", len(checkpoints))
	}

	// Verify checkpoint details
	foundCp1 := false
	foundCp2 := false
	for _, cp := range checkpoints {
		if cp.ID == "checkpoint-1" {
			foundCp1 = true
			if cp.SourceID != "" {
				t.Errorf("checkpoint-1 should not have a source ID, got %s", cp.SourceID)
			}
		} else if cp.ID == "checkpoint-2" {
			foundCp2 = true
			if cp.SourceID != "checkpoint-1" {
				t.Errorf("checkpoint-2 should have source ID 'checkpoint-1', got %s", cp.SourceID)
			}
		}
	}

	if !foundCp1 {
		t.Error("checkpoint-1 not found in list")
	}
	if !foundCp2 {
		t.Error("checkpoint-2 not found in list")
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
	cpDir := filepath.Join(checkpointsDir, "test-checkpoint")
	if err := os.MkdirAll(cpDir, 0755); err != nil {
		t.Fatalf("Failed to create checkpoint directory: %v", err)
	}

	// Add source file
	sourceFile := filepath.Join(cpDir, ".source")
	if err := os.WriteFile(sourceFile, []byte("original-checkpoint"), 0644); err != nil {
		t.Fatalf("Failed to write source file: %v", err)
	}

	// Test getting checkpoint
	checkpoint, err := jfs.GetCheckpoint(ctx, "test-checkpoint")
	if err != nil {
		t.Fatalf("Failed to get checkpoint: %v", err)
	}

	if checkpoint.ID != "test-checkpoint" {
		t.Errorf("Expected ID 'test-checkpoint', got %s", checkpoint.ID)
	}

	if checkpoint.SourceID != "original-checkpoint" {
		t.Errorf("Expected source ID 'original-checkpoint', got %s", checkpoint.SourceID)
	}

	// Test empty checkpoint ID
	_, err = jfs.GetCheckpoint(ctx, "")
	if err == nil {
		t.Error("Expected error for empty checkpoint ID")
	}
}
