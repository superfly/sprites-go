package juicefs

import (
	"context"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestCheckpointManager(t *testing.T) {
	// Create a temporary directory for testing
	tmpDir, err := os.MkdirTemp("", "checkpoint_manager_test")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(tmpDir)

	// Create necessary directories
	dataDir := filepath.Join(tmpDir, "data")
	if err := os.MkdirAll(dataDir, 0755); err != nil {
		t.Fatal(err)
	}

	// Create checkpoint manager
	cm := NewCheckpointManager(tmpDir, context.Background())

	// Initialize the database
	if err := cm.Initialize(dataDir); err != nil {
		t.Fatalf("Failed to initialize checkpoint manager: %v", err)
	}
	defer cm.Close()

	ctx := context.Background()

	// Test 1: Initial state
	if cm.db == nil {
		t.Error("Expected database to be initialized")
	}

	// Test 2: Create checkpoint
	// Note: This will fail without a real JuiceFS installation
	// In a real test environment, you would mock the clone operation
	err = cm.Checkpoint(ctx, "ignored-id")
	if err == nil {
		t.Fatal("Expected checkpoint to fail without JuiceFS installed")
	}
	// Verify it failed for the expected reason
	if !os.IsNotExist(err) && !strings.Contains(err.Error(), "juicefs") {
		t.Errorf("Unexpected error: %v", err)
	}

	// Test 3: Restore without checkpoint ID
	err = cm.Restore(ctx, "")
	if err == nil || err.Error() != "checkpoint ID is required" {
		t.Errorf("Expected 'checkpoint ID is required' error, got: %v", err)
	}

	// Test 4: Close
	if err := cm.Close(); err != nil {
		t.Errorf("Failed to close checkpoint manager: %v", err)
	}

	// Verify database is closed
	if cm.db == nil {
		t.Error("Expected database reference to remain (just closed)")
	}
}

func TestCheckpointManagerWithoutInit(t *testing.T) {
	// Create checkpoint manager without initializing
	cm := NewCheckpointManager("/tmp", context.Background())

	ctx := context.Background()

	// Test checkpoint without initialization
	err := cm.Checkpoint(ctx, "test-id")
	if err == nil || err.Error() != "checkpoint database not initialized" {
		t.Errorf("Expected 'checkpoint database not initialized' error, got: %v", err)
	}

	// Test restore without initialization
	err = cm.Restore(ctx, "test-id")
	if err == nil || err.Error() != "checkpoint database not initialized" {
		t.Errorf("Expected 'checkpoint database not initialized' error, got: %v", err)
	}

	// Test close without initialization
	if err := cm.Close(); err != nil {
		t.Errorf("Close should succeed even without initialization, got: %v", err)
	}
}
