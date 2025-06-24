package juicefs

import (
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
	db, err := NewCheckpointDB(tmpDir)
	if err != nil {
		t.Fatalf("Failed to create checkpoint database: %v", err)
	}
	defer db.Close()

	// Test 1: Initial v0 checkpoint should exist
	latest, err := db.GetLatestCheckpoint()
	if err != nil {
		t.Fatalf("Failed to get latest checkpoint: %v", err)
	}
	if latest.ID != 1 {
		t.Errorf("Expected initial checkpoint ID to be 1, got %d", latest.ID)
	}
	if latest.Path != "active/" {
		t.Errorf("Expected initial checkpoint path to be 'active/', got %s", latest.Path)
	}
	if latest.ParentID.Valid {
		t.Errorf("Expected initial checkpoint to have no parent")
	}

	// Test 2: Create a checkpoint
	cloneExecuted := false
	var cloneSrc, cloneDst string
	
	newCheckpoint, err := db.CreateCheckpoint(func(src, dst string) error {
		cloneExecuted = true
		cloneSrc = src
		cloneDst = dst
		return nil
	})
	if err != nil {
		t.Fatalf("Failed to create checkpoint: %v", err)
	}

	if !cloneExecuted {
		t.Error("Clone function was not executed")
	}
	if cloneSrc != "active/" {
		t.Errorf("Expected clone source to be 'active/', got %s", cloneSrc)
	}
	if cloneDst != "checkpoints/v0" {
		t.Errorf("Expected clone destination to be 'checkpoints/v0', got %s", cloneDst)
	}

	// Verify the new checkpoint
	if newCheckpoint.ID != 2 {
		t.Errorf("Expected new checkpoint ID to be 2, got %d", newCheckpoint.ID)
	}
	if newCheckpoint.Path != "active/" {
		t.Errorf("Expected new checkpoint path to be 'active/', got %s", newCheckpoint.Path)
	}
	if !newCheckpoint.ParentID.Valid || newCheckpoint.ParentID.Int64 != 1 {
		t.Errorf("Expected new checkpoint parent ID to be 1, got %v", newCheckpoint.ParentID)
	}

	// Test 3: Verify the previous checkpoint was updated
	prevCheckpoint, err := db.GetCheckpointByID(1)
	if err != nil {
		t.Fatalf("Failed to get checkpoint by ID: %v", err)
	}
	if prevCheckpoint.Path != "checkpoints/v0" {
		t.Errorf("Expected previous checkpoint path to be updated to 'checkpoints/v0', got %s", prevCheckpoint.Path)
	}

	// Test 4: Find checkpoint by path
	found, err := db.FindCheckpointByPath("checkpoints/v0")
	if err != nil {
		t.Fatalf("Failed to find checkpoint by path: %v", err)
	}
	if found.ID != 1 {
		t.Errorf("Expected found checkpoint ID to be 1, got %d", found.ID)
	}

	// Test 5: Create another checkpoint
	newCheckpoint2, err := db.CreateCheckpoint(func(src, dst string) error {
		if dst != "checkpoints/v1" {
			t.Errorf("Expected second checkpoint destination to be 'checkpoints/v1', got %s", dst)
		}
		return nil
	})
	if err != nil {
		t.Fatalf("Failed to create second checkpoint: %v", err)
	}
	if newCheckpoint2.ID != 3 {
		t.Errorf("Expected second new checkpoint ID to be 3, got %d", newCheckpoint2.ID)
	}
	if !newCheckpoint2.ParentID.Valid || newCheckpoint2.ParentID.Int64 != 2 {
		t.Errorf("Expected second new checkpoint parent ID to be 2, got %v", newCheckpoint2.ParentID)
	}
}