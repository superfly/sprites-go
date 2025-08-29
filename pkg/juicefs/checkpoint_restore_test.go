package juicefs

import (
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"testing"
)

// TestRestoreV0Checkpoint tests restoring from the initial empty v0 checkpoint
func TestRestoreV0Checkpoint(t *testing.T) {
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

	// Initialize mount path and database
	mountPath := filepath.Join(tmpDir, "data")
	if err := os.MkdirAll(mountPath, 0755); err != nil {
		t.Fatalf("Failed to create mount path: %v", err)
	}

	db, err := NewCheckpointDB(CheckpointDBConfig{
		BaseDir: tmpDir,
	})
	if err != nil {
		t.Fatalf("Failed to create checkpoint database: %v", err)
	}
	jfs.checkpointDB = db
	defer db.Close()

	ctx := context.Background()

	// Create the directory structure that would exist after mount
	checkpointsDir := filepath.Join(mountPath, "checkpoints")
	if err := os.MkdirAll(checkpointsDir, 0755); err != nil {
		t.Fatalf("Failed to create checkpoints directory: %v", err)
	}

	// Create empty v0 directory
	v0Dir := filepath.Join(checkpointsDir, "v0")
	if err := os.MkdirAll(v0Dir, 0755); err != nil {
		t.Fatalf("Failed to create v0 directory: %v", err)
	}

	// Create active directory with some content
	activeDir := filepath.Join(mountPath, "active")
	activeFsDir := filepath.Join(activeDir, "fs")
	if err := os.MkdirAll(activeFsDir, 0755); err != nil {
		t.Fatalf("Failed to create active directory: %v", err)
	}

	// Add test content to active directory
	testFile := filepath.Join(activeFsDir, "test.txt")
	if err := os.WriteFile(testFile, []byte("test content"), 0644); err != nil {
		t.Fatalf("Failed to write test file: %v", err)
	}

	// Verify v0 checkpoint exists in database
	checkpoints, err := jfs.ListCheckpoints(ctx)
	if err != nil {
		t.Fatalf("Failed to list checkpoints: %v", err)
	}

	foundV0 := false
	for _, cp := range checkpoints {
		if cp.ID == "v0" {
			foundV0 = true
			break
		}
	}
	if !foundV0 {
		t.Fatal("v0 checkpoint not found in list")
	}

	// Test restoring from v0
	t.Run("RestoreEmptyV0", func(t *testing.T) {
		// Allow tests to run without juicefs when JUICEFS_CLONE_CMD is set
		if os.Getenv("JUICEFS_CLONE_CMD") == "" {
			if _, err := exec.LookPath("juicefs"); err != nil {
				t.Skip("juicefs command not found in PATH, skipping restore test")
			}
		}

		err := jfs.Restore(ctx, "v0")
		if err != nil {
			// This is the expected failure we're trying to fix
			t.Logf("Restore from v0 failed (expected in current implementation): %v", err)

			// Check if it's because juicefs clone fails with empty directory
			if os.IsNotExist(err) || contains(err.Error(), "clone") {
				t.Logf("Confirmed: v0 restore fails due to empty checkpoint directory")
			}
		} else {
			// If restore succeeds, verify the active directory is empty
			entries, err := os.ReadDir(activeDir)
			if err != nil {
				t.Errorf("Failed to read active directory after restore: %v", err)
			} else if len(entries) > 0 {
				// We expect only the 'fs' subdirectory to exist
				if len(entries) != 1 || entries[0].Name() != "fs" {
					t.Errorf("Expected empty active directory after v0 restore, found %d entries", len(entries))
				} else {
					// Check if fs directory is empty
					fsEntries, err := os.ReadDir(activeFsDir)
					if err != nil {
						t.Errorf("Failed to read fs directory: %v", err)
					} else if len(fsEntries) > 0 {
						t.Errorf("Expected empty fs directory after v0 restore, found %d entries", len(fsEntries))
					}
				}
			}
		}
	})
}

// TestCheckpointRestoreCycle tests a full checkpoint and restore cycle
func TestCheckpointRestoreCycle(t *testing.T) {
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

	// Initialize mount path and database
	mountPath := filepath.Join(tmpDir, "data")
	if err := os.MkdirAll(mountPath, 0755); err != nil {
		t.Fatalf("Failed to create mount path: %v", err)
	}

	db, err := NewCheckpointDB(CheckpointDBConfig{
		BaseDir: tmpDir,
	})
	if err != nil {
		t.Fatalf("Failed to create checkpoint database: %v", err)
	}
	jfs.checkpointDB = db
	defer db.Close()

	ctx := context.Background()

	// Use simple copy for clone in tests
	t.Setenv("JUICEFS_CLONE_CMD", "cp -R")

	// Create the directory structure
	checkpointsDir := filepath.Join(mountPath, "checkpoints")
	if err := os.MkdirAll(checkpointsDir, 0755); err != nil {
		t.Fatalf("Failed to create checkpoints directory: %v", err)
	}

	// Create v0 directory
	v0Dir := filepath.Join(checkpointsDir, "v0")
	if err := os.MkdirAll(v0Dir, 0755); err != nil {
		t.Fatalf("Failed to create v0 directory: %v", err)
	}

	// Create active directory
	activeDir := filepath.Join(mountPath, "active")
	activeFsDir := filepath.Join(activeDir, "fs")
	if err := os.MkdirAll(activeFsDir, 0755); err != nil {
		t.Fatalf("Failed to create active directory: %v", err)
	}

	// Skip only if neither JUICEFS_CLONE_CMD is set nor juicefs is available
	if os.Getenv("JUICEFS_CLONE_CMD") == "" {
		if _, err := exec.LookPath("juicefs"); err != nil {
			t.Skip("juicefs command not found in PATH, skipping checkpoint/restore cycle test")
		}
	}

	// Test 1: Create checkpoint from initial state
	t.Run("CheckpointInitialState", func(t *testing.T) {
		// Add a test file
		testFile := filepath.Join(activeFsDir, "initial.txt")
		if err := os.WriteFile(testFile, []byte("initial content"), 0644); err != nil {
			t.Fatalf("Failed to write initial file: %v", err)
		}

		// Create checkpoint (should be v1)
		err := jfs.Checkpoint(ctx, "")
		if err != nil {
			t.Fatalf("Failed to create checkpoint: %v", err)
		}

		// Verify checkpoint was created
		v1Dir := filepath.Join(checkpointsDir, "v1")
		if _, err := os.Stat(v1Dir); os.IsNotExist(err) {
			t.Errorf("v1 checkpoint directory was not created")
		}
	})

	// Test 2: Modify state and create another checkpoint
	t.Run("CheckpointModifiedState", func(t *testing.T) {
		// Modify the file
		testFile := filepath.Join(activeFsDir, "initial.txt")
		if err := os.WriteFile(testFile, []byte("modified content"), 0644); err != nil {
			t.Fatalf("Failed to modify file: %v", err)
		}

		// Add another file
		testFile2 := filepath.Join(activeFsDir, "second.txt")
		if err := os.WriteFile(testFile2, []byte("second file"), 0644); err != nil {
			t.Fatalf("Failed to write second file: %v", err)
		}

		// Create checkpoint (should be v2)
		err := jfs.Checkpoint(ctx, "")
		if err != nil {
			t.Fatalf("Failed to create checkpoint: %v", err)
		}
	})

	// Test 3: Restore to v1
	t.Run("RestoreToV1", func(t *testing.T) {
		err := jfs.Restore(ctx, "v1")
		if err != nil {
			t.Fatalf("Failed to restore to v1: %v", err)
		}

		// Verify first file has original content
		testFile := filepath.Join(activeFsDir, "initial.txt")
		content, err := os.ReadFile(testFile)
		if err != nil {
			t.Fatalf("Failed to read restored file: %v", err)
		}
		if string(content) != "initial content" {
			t.Errorf("Restored file has wrong content: %s", string(content))
		}

		// Verify second file doesn't exist
		testFile2 := filepath.Join(activeFsDir, "second.txt")
		if _, err := os.Stat(testFile2); !os.IsNotExist(err) {
			t.Errorf("Second file should not exist after restoring to v1")
		}
	})

	// Test 4: Test various checkpoint ID formats
	t.Run("RestoreWithDifferentIDFormats", func(t *testing.T) {
		// These should all work
		testCases := []string{
			"v1",             // Version format
			"checkpoints/v1", // Full path format
		}

		for _, checkpointID := range testCases {
			err := jfs.Restore(ctx, checkpointID)
			if err != nil {
				t.Errorf("Failed to restore with checkpoint ID %s: %v", checkpointID, err)
			}
		}
	})
}

// TestRestoreNonExistentCheckpoint tests error handling for invalid checkpoints
func TestRestoreNonExistentCheckpoint(t *testing.T) {
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

	// Initialize database
	db, err := NewCheckpointDB(CheckpointDBConfig{
		BaseDir: tmpDir,
	})
	if err != nil {
		t.Fatalf("Failed to create checkpoint database: %v", err)
	}
	jfs.checkpointDB = db
	defer db.Close()

	ctx := context.Background()

	// Test restoring non-existent checkpoint
	err = jfs.Restore(ctx, "v999")
	if err == nil {
		t.Error("Expected error when restoring non-existent checkpoint")
	} else if !contains(err.Error(), "not found") {
		t.Errorf("Expected 'not found' error, got: %v", err)
	}
}

// TestRestoreWithEmptyDirectory tests that we can properly handle empty checkpoint directories
func TestRestoreWithEmptyDirectory(t *testing.T) {
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

	// Initialize mount path and database
	mountPath := filepath.Join(tmpDir, "data")
	if err := os.MkdirAll(mountPath, 0755); err != nil {
		t.Fatalf("Failed to create mount path: %v", err)
	}

	db, err := NewCheckpointDB(CheckpointDBConfig{
		BaseDir: tmpDir,
	})
	if err != nil {
		t.Fatalf("Failed to create checkpoint database: %v", err)
	}
	jfs.checkpointDB = db
	defer db.Close()

	ctx := context.Background()

	// Create checkpoints directory
	checkpointsDir := filepath.Join(mountPath, "checkpoints")
	if err := os.MkdirAll(checkpointsDir, 0755); err != nil {
		t.Fatalf("Failed to create checkpoints directory: %v", err)
	}

	// Create an empty checkpoint directory and register it
	emptyDir := filepath.Join(checkpointsDir, "v_empty")
	if err := os.MkdirAll(emptyDir, 0755); err != nil {
		t.Fatalf("Failed to create empty checkpoint directory: %v", err)
	}

	// Add to database
	_, err = db.db.Exec("INSERT INTO sprite_checkpoints (path, parent_id) VALUES (?, ?)", "checkpoints/v_empty", nil)
	if err != nil {
		t.Fatalf("Failed to insert empty checkpoint: %v", err)
	}

	// Create active directory with content
	activeDir := filepath.Join(mountPath, "active")
	activeFsDir := filepath.Join(activeDir, "fs")
	if err := os.MkdirAll(activeFsDir, 0755); err != nil {
		t.Fatalf("Failed to create active directory: %v", err)
	}

	testFile := filepath.Join(activeFsDir, "test.txt")
	if err := os.WriteFile(testFile, []byte("test content"), 0644); err != nil {
		t.Fatalf("Failed to write test file: %v", err)
	}

	// Skip if juicefs is not available
	if _, err := exec.LookPath("juicefs"); err != nil {
		t.Skip("juicefs command not found in PATH, skipping empty directory restore test")
	}

	// Test restoring from empty checkpoint
	err = jfs.Restore(ctx, "v_empty")
	if err != nil {
		t.Logf("Restore from empty checkpoint failed: %v", err)
		// This is expected with current implementation
		// TODO: Fix this to handle empty checkpoints gracefully
	}
}
