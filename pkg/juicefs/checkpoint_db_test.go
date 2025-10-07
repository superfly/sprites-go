package juicefs

import (
	"fmt"
	"os"
	"testing"
)

func TestCheckpointDB(t *testing.T) {
	// Create a temporary directory for testing
	tmpDir, err := os.MkdirTemp("", "checkpoint_db_test")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(tmpDir)

	// Create checkpoint database
	db, err := NewCheckpointDB(CheckpointDBConfig{
		BaseDir: tmpDir,
	})
	if err != nil {
		t.Fatalf("Failed to create checkpoint database: %v", err)
	}
	defer db.Close()

	// Test 1: Initial v1 checkpoint should exist (latest should be the active record)
	latest, err := db.GetLatestCheckpoint()
	if err != nil {
		t.Fatalf("Failed to get latest checkpoint: %v", err)
	}
	if latest.ID != 2 {
		t.Errorf("Expected initial checkpoint ID to be 2, got %d", latest.ID)
	}
	if latest.Path != "active/" {
		t.Errorf("Expected initial checkpoint path to be 'active/', got %s", latest.Path)
	}
	if !latest.ParentID.Valid || latest.ParentID.Int64 != 1 {
		t.Errorf("Expected initial checkpoint to have parent ID 1, got %v", latest.ParentID)
	}

	// Test 2: Create a checkpoint
	cloneExecuted := false
	renameExecuted := false

	newCheckpoint, err := db.CreateCheckpoint(
		func(src, dst string) error {
			cloneExecuted = true
			// For testing, just verify the paths (now should be v1.in-progress since we start with v1)
			if src != "active/" || dst != "checkpoints/v1.in-progress" {
				return fmt.Errorf("unexpected paths: src=%s, dst=%s", src, dst)
			}
			return nil
		},
		func(src, dst string) error {
			renameExecuted = true
			// For testing, verify the rename operation
			if dst == "" {
				// Cleanup
				return nil
			}
			if src != "checkpoints/v1.in-progress" || dst != "checkpoints/v1" {
				return fmt.Errorf("unexpected rename: src=%s, dst=%s", src, dst)
			}
			return nil
		},
	)
	if err != nil {
		t.Fatalf("Failed to create checkpoint: %v", err)
	}

	if !cloneExecuted {
		t.Error("Clone function was not executed")
	}
	if !renameExecuted {
		t.Error("Rename function was not executed")
	}

	// Verify the new checkpoint - it should be the record that was updated to become the checkpoint
	if newCheckpoint.ID != 2 {
		t.Errorf("Expected new checkpoint ID to be 2, got %d", newCheckpoint.ID)
	}
	if newCheckpoint.Path != "checkpoints/v1" {
		t.Errorf("Expected new checkpoint path to be 'checkpoints/v1', got %s", newCheckpoint.Path)
	}
	if !newCheckpoint.ParentID.Valid || newCheckpoint.ParentID.Int64 != 1 {
		t.Errorf("Expected new checkpoint parent ID to be 1, got %v", newCheckpoint.ParentID)
	}

	// Test 3: Verify the new active record was created
	activeRecord, err := db.GetCheckpointByID(3)
	if err != nil {
		t.Fatalf("Failed to get active record by ID: %v", err)
	}
	if activeRecord.Path != "active/" {
		t.Errorf("Expected new active record path to be 'active/', got %s", activeRecord.Path)
	}
	if !activeRecord.ParentID.Valid || activeRecord.ParentID.Int64 != 2 {
		t.Errorf("Expected new active record parent ID to be 2, got %v", activeRecord.ParentID)
	}

	// Test 4: Find checkpoint by path
	found, err := db.FindCheckpointByPath("checkpoints/v1")
	if err != nil {
		t.Fatalf("Failed to find checkpoint by path: %v", err)
	}
	if found.ID != 2 {
		t.Errorf("Expected found checkpoint ID to be 2, got %d", found.ID)
	}

	// Test 5: Create another checkpoint
	newCheckpoint2, err := db.CreateCheckpoint(
		func(src, dst string) error {
			if dst != "checkpoints/v2.in-progress" {
				t.Errorf("Expected second checkpoint destination to be 'checkpoints/v2.in-progress', got %s", dst)
			}
			return nil
		},
		func(src, dst string) error {
			if dst != "" && dst != "checkpoints/v2" {
				t.Errorf("Expected rename destination to be 'checkpoints/v2', got %s", dst)
			}
			return nil
		},
	)
	if err != nil {
		t.Fatalf("Failed to create second checkpoint: %v", err)
	}
	// The second checkpoint should be the record that was updated (ID=3)
	if newCheckpoint2.ID != 3 {
		t.Errorf("Expected second new checkpoint ID to be 3, got %d", newCheckpoint2.ID)
	}
	if !newCheckpoint2.ParentID.Valid || newCheckpoint2.ParentID.Int64 != 2 {
		t.Errorf("Expected second new checkpoint parent ID to be 2, got %v", newCheckpoint2.ParentID)
	}
}
