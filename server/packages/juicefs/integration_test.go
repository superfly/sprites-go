//go:build integration
// +build integration

package juicefs_test

import (
	"context"
	"os"
	"path/filepath"
	"testing"
	"time"

	"github.com/fly-dev-env/sprite-env/server/packages/juicefs"
)

// TestJuiceFSLocalModeIntegration tests JuiceFS in local mode
// Run with: go test -tags=integration -v
func TestJuiceFSLocalModeIntegration(t *testing.T) {
	// Skip if juicefs binary is not available
	if _, err := os.Stat("/usr/local/bin/juicefs"); os.IsNotExist(err) {
		t.Skip("juicefs binary not found, skipping integration test")
	}

	tmpDir := t.TempDir()

	config := juicefs.Config{
		BaseDir:    tmpDir,
		LocalMode:  true,
		VolumeName: "test-volume",
	}

	jfs, err := juicefs.New(config)
	if err != nil {
		t.Fatalf("Failed to create JuiceFS: %v", err)
	}

	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	// Start JuiceFS
	if err := jfs.Start(ctx); err != nil {
		t.Fatalf("Failed to start JuiceFS: %v", err)
	}

	// Verify the filesystem is mounted and ready
	activeDir := filepath.Join(tmpDir, "data", "active", "fs")
	if _, err := os.Stat(activeDir); os.IsNotExist(err) {
		t.Errorf("Active directory was not created: %s", activeDir)
	}

	// Create a test file
	testFile := filepath.Join(activeDir, "test.txt")
	testContent := []byte("Hello, JuiceFS!")
	if err := os.WriteFile(testFile, testContent, 0644); err != nil {
		t.Fatalf("Failed to write test file: %v", err)
	}

	// Create a checkpoint
	checkpointID := "test-checkpoint-1"
	if err := jfs.Checkpoint(ctx, checkpointID); err != nil {
		t.Fatalf("Failed to create checkpoint: %v", err)
	}

	// Modify the file
	newContent := []byte("Modified content")
	if err := os.WriteFile(testFile, newContent, 0644); err != nil {
		t.Fatalf("Failed to modify test file: %v", err)
	}

	// Restore from checkpoint
	if err := jfs.Restore(ctx, checkpointID); err != nil {
		t.Fatalf("Failed to restore from checkpoint: %v", err)
	}

	// Verify the file was restored
	restoredContent, err := os.ReadFile(testFile)
	if err != nil {
		t.Fatalf("Failed to read restored file: %v", err)
	}

	if string(restoredContent) != string(testContent) {
		t.Errorf("Restored content mismatch: got %q, want %q", restoredContent, testContent)
	}

	// Stop JuiceFS
	if err := jfs.Stop(ctx); err != nil {
		t.Fatalf("Failed to stop JuiceFS: %v", err)
	}

	// Verify Litestream created local backups
	litestreamDir := filepath.Join(tmpDir, "litestream")
	if _, err := os.Stat(litestreamDir); os.IsNotExist(err) {
		t.Logf("Warning: Litestream directory not found (may not have had time to create backups)")
	}
}
