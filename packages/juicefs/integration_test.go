//go:build integration
// +build integration

package juicefs_test

import (
	"context"
	"fmt"
	"log/slog"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/sprite-env/packages/juicefs"
)

// TestJuiceFSLocalModeIntegration tests JuiceFS in local mode
// Run with: go test -tags=integration -v
func TestJuiceFSLocalModeIntegration(t *testing.T) {
	// Skip if juicefs binary is not available
	if _, err := os.Stat("/usr/local/bin/juicefs"); os.IsNotExist(err) {
		t.Skip("juicefs binary not found, skipping integration test")
	}

	// Use manual temp directory to control cleanup timing
	tmpDir, tmpErr := os.MkdirTemp("", "TestJuiceFSLocalModeIntegration")
	if tmpErr != nil {
		t.Fatalf("Failed to create temp dir: %v", tmpErr)
	}
	defer func() {
		// Wait for kernel to clean up FUSE mount before removing directory
		time.Sleep(200 * time.Millisecond)
		os.RemoveAll(tmpDir)
	}()

	// Create a logger for detailed output
	logger := slog.New(slog.NewTextHandler(os.Stderr, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))

	config := juicefs.Config{
		BaseDir:    tmpDir,
		LocalMode:  true,
		VolumeName: "test-volume",
		Logger:     logger,
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

	// Test checkpoint
	t.Run("Checkpoint", func(t *testing.T) {
		// Create checkpoint (version will be auto-generated)
		err := jfs.Checkpoint(ctx, "")
		if err != nil {
			t.Fatalf("Failed to create checkpoint: %v", err)
		}

		// List checkpoints to verify
		checkpoints, err := jfs.ListCheckpoints(ctx)
		if err != nil {
			t.Fatalf("Failed to list checkpoints: %v", err)
		}

		if len(checkpoints) != 2 {
			t.Fatalf("Expected 2 checkpoints (v0 initial + v1 created), got %d", len(checkpoints))
		}

		// The first checkpoint created should be v1 (v0 is the initial empty one)
		// Checkpoints are returned in reverse order, so v1 should be first
		foundV1 := false
		for _, cp := range checkpoints {
			if cp.ID == "v1" {
				foundV1 = true
				break
			}
		}
		if !foundV1 {
			t.Errorf("Expected to find v1 checkpoint, available checkpoints: %v", checkpoints)
		}

		// Test restore
		t.Run("Restore", func(t *testing.T) {
			// Restore from v1 (the checkpoint we just created)
			err := jfs.Restore(ctx, "v1")
			if err != nil {
				t.Fatalf("Failed to restore checkpoint: %v", err)
			}

			// Verify the restore was successful by checking file content
			restoredTestFile := filepath.Join(tmpDir, "data", "active", "fs", "test.txt")
			if _, err := os.Stat(restoredTestFile); os.IsNotExist(err) {
				t.Errorf("Test file was not restored after checkpoint restore")
			}

			// Give quota application time to run after restore
			time.Sleep(3 * time.Second)

			// Verify quota was applied after restore
			metaDB := filepath.Join(tmpDir, "metadata.db")
			metaURL := fmt.Sprintf("sqlite3://%s", metaDB)

			quotaCmd := exec.Command("juicefs", "quota", "get", metaURL, "--path", "/active/fs")
			output, err := quotaCmd.CombinedOutput()

			if err != nil {
				t.Logf("Quota check after restore - output: %s", string(output))
				t.Logf("Warning: Could not verify quota after restore: %v", err)
			} else {
				outputStr := string(output)
				if strings.Contains(outputStr, "10 TiB") || strings.Contains(outputStr, "10240 GiB") {
					t.Logf("Successfully verified 10TB quota on /active/fs after restore")
				} else {
					t.Logf("Quota output after restore: %s", outputStr)
					t.Errorf("Expected 10TB quota not found after restore")
				}
			}
		})
	})

	// Modify the file
	newContent := []byte("Modified content")
	if err := os.WriteFile(testFile, newContent, 0644); err != nil {
		t.Fatalf("Failed to modify test file: %v", err)
	}

	// Restore from checkpoint
	if err := jfs.Restore(ctx, "v1"); err != nil {
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

	// Stop JuiceFS with a timeout that accounts for the full shutdown process
	// JuiceFS unmount can take up to 5 minutes, plus Litestream 1 minute, plus buffer
	stopCtx, stopCancel := context.WithTimeout(context.Background(), 7*time.Minute)
	defer stopCancel()

	if err := jfs.Stop(stopCtx); err != nil {
		t.Fatalf("Failed to stop JuiceFS: %v", err)
	}

	// Verify Litestream created local backups
	litestreamDir := filepath.Join(tmpDir, "litestream")
	if _, err := os.Stat(litestreamDir); os.IsNotExist(err) {
		t.Logf("Warning: Litestream directory not found (may not have had time to create backups)")
	}
}
