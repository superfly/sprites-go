package juicefs

import (
	"context"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

func TestVersionManagement(t *testing.T) {
	tmpDir := t.TempDir()

	config := Config{
		BaseDir:           tmpDir,
		S3AccessKey:       "test",
		S3SecretAccessKey: "test",
		S3EndpointURL:     "http://localhost:9000",
		S3Bucket:          "test",
		VolumeName:        "test-volume",
	}

	jfs, err := New(config)
	if err != nil {
		t.Fatalf("Failed to create JuiceFS: %v", err)
	}

	// Simulate mount path and active directory creation
	mountPath := filepath.Join(tmpDir, "data")
	activeDir := filepath.Join(mountPath, "active")
	if err := os.MkdirAll(activeDir, 0755); err != nil {
		t.Fatalf("Failed to create active directory: %v", err)
	}

	t.Run("InitializeVersion", func(t *testing.T) {
		// Initialize version should create v0
		if err := jfs.initializeVersion(); err != nil {
			t.Fatalf("Failed to initialize version: %v", err)
		}

		// Check version file exists
		versionFile := filepath.Join(activeDir, ".version")
		data, err := os.ReadFile(versionFile)
		if err != nil {
			t.Fatalf("Failed to read version file: %v", err)
		}

		if string(data) != "v0\n" {
			t.Errorf("Expected initial version to be v0, got %s", string(data))
		}

		// Re-initializing should be idempotent
		if err := jfs.initializeVersion(); err != nil {
			t.Fatalf("Re-initialize failed: %v", err)
		}

		// Version should still be v0
		data, err = os.ReadFile(versionFile)
		if err != nil {
			t.Fatalf("Failed to read version file after re-init: %v", err)
		}

		if string(data) != "v0\n" {
			t.Errorf("Version changed after re-init, got %s", string(data))
		}
	})

	t.Run("GetCurrentVersion", func(t *testing.T) {
		version, err := jfs.GetCurrentVersion()
		if err != nil {
			t.Fatalf("Failed to get current version: %v", err)
		}

		if version != 0 {
			t.Errorf("Expected current version to be 0, got %d", version)
		}
	})

	t.Run("AppendToHistory", func(t *testing.T) {
		// Append first restore record
		if err := jfs.appendToHistory("v0"); err != nil {
			t.Fatalf("Failed to append to history: %v", err)
		}

		historyFile := filepath.Join(activeDir, ".history")
		data, err := os.ReadFile(historyFile)
		if err != nil {
			t.Fatalf("Failed to read history file: %v", err)
		}

		lines := strings.Split(strings.TrimSpace(string(data)), "\n")
		if len(lines) != 1 {
			t.Errorf("Expected 1 history line, got %d", len(lines))
		}

		// Check format
		if !strings.HasPrefix(lines[0], "to=v0;time=") {
			t.Errorf("Invalid history format: %s", lines[0])
		}

		// Parse time to ensure it's valid RFC3339
		parts := strings.Split(lines[0], ";time=")
		if len(parts) != 2 {
			t.Fatalf("Failed to parse history line: %s", lines[0])
		}

		_, err = time.Parse(time.RFC3339, parts[1])
		if err != nil {
			t.Errorf("Invalid timestamp format: %s", parts[1])
		}

		// Append second restore record
		time.Sleep(10 * time.Millisecond) // Ensure different timestamp
		if err := jfs.appendToHistory("v1"); err != nil {
			t.Fatalf("Failed to append second history: %v", err)
		}

		data, err = os.ReadFile(historyFile)
		if err != nil {
			t.Fatalf("Failed to read history file after second append: %v", err)
		}

		lines = strings.Split(strings.TrimSpace(string(data)), "\n")
		if len(lines) != 2 {
			t.Errorf("Expected 2 history lines, got %d", len(lines))
		}

		// Check second line format
		if !strings.HasPrefix(lines[1], "to=v1;time=") {
			t.Errorf("Invalid second history format: %s", lines[1])
		}
	})
}

func TestListCheckpointsWithHistory(t *testing.T) {
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

	// Create test checkpoint structure
	mountPath := filepath.Join(tmpDir, "data")
	checkpointsDir := filepath.Join(mountPath, "checkpoints")
	activeDir := filepath.Join(mountPath, "active")

	// Create active directory with history
	if err := os.MkdirAll(activeDir, 0755); err != nil {
		t.Fatalf("Failed to create active directory: %v", err)
	}

	activeHistory := filepath.Join(activeDir, ".history")
	activeHistoryContent := "to=v0;time=2024-01-15T09:00:00Z\nto=v2;time=2024-01-15T13:00:00Z\n"
	if err := os.WriteFile(activeHistory, []byte(activeHistoryContent), 0644); err != nil {
		t.Fatalf("Failed to write active history: %v", err)
	}

	// Create v0 checkpoint
	v0Dir := filepath.Join(checkpointsDir, "v0")
	if err := os.MkdirAll(v0Dir, 0755); err != nil {
		t.Fatalf("Failed to create v0 directory: %v", err)
	}

	// Create v1 checkpoint with history showing it was restored to v0
	v1Dir := filepath.Join(checkpointsDir, "v1")
	if err := os.MkdirAll(v1Dir, 0755); err != nil {
		t.Fatalf("Failed to create v1 directory: %v", err)
	}

	v1History := filepath.Join(v1Dir, ".history")
	historyContent := "to=v0;time=2024-01-15T10:00:00Z\n"
	if err := os.WriteFile(v1History, []byte(historyContent), 0644); err != nil {
		t.Fatalf("Failed to write v1 history: %v", err)
	}

	// Create v2 checkpoint also restored to v0 and v1
	v2Dir := filepath.Join(checkpointsDir, "v2")
	if err := os.MkdirAll(v2Dir, 0755); err != nil {
		t.Fatalf("Failed to create v2 directory: %v", err)
	}

	v2History := filepath.Join(v2Dir, ".history")
	historyContent2 := "to=v0;time=2024-01-15T11:00:00Z\nto=v1;time=2024-01-15T12:00:00Z\n"
	if err := os.WriteFile(v2History, []byte(historyContent2), 0644); err != nil {
		t.Fatalf("Failed to write v2 history: %v", err)
	}

	// Test ListCheckpointsWithHistory for v0
	results, err := jfs.ListCheckpointsWithHistory(context.Background(), "v0")
	if err != nil {
		t.Fatalf("Failed to list checkpoints with history: %v", err)
	}

	if len(results) != 3 {
		t.Errorf("Expected 3 results for v0 history, got %d", len(results))
		for i, r := range results {
			t.Logf("Result %d: %s", i, r)
		}
	}

	// Check results format
	expectedPrefixes := []string{
		"active/.history: to=v0;time=",
		"v1/.history: to=v0;time=",
		"v2/.history: to=v0;time=",
	}

	for _, prefix := range expectedPrefixes {
		found := false
		for _, result := range results {
			if strings.HasPrefix(result, prefix) {
				found = true
				break
			}
		}
		if !found {
			t.Errorf("Did not find result with prefix: %s", prefix)
		}
	}

	// Test ListCheckpointsWithHistory for v1
	results, err = jfs.ListCheckpointsWithHistory(context.Background(), "v1")
	if err != nil {
		t.Fatalf("Failed to list checkpoints with v1 history: %v", err)
	}

	if len(results) != 1 {
		t.Errorf("Expected 1 result for v1 history, got %d", len(results))
	}

	if len(results) > 0 && !strings.Contains(results[0], "v2/.history: to=v1;time=") {
		t.Errorf("Unexpected result format: %s", results[0])
	}

	// Test ListCheckpointsWithHistory for v2
	results, err = jfs.ListCheckpointsWithHistory(context.Background(), "v2")
	if err != nil {
		t.Fatalf("Failed to list checkpoints with v2 history: %v", err)
	}

	if len(results) != 1 {
		t.Errorf("Expected 1 result for v2 history, got %d", len(results))
		for i, r := range results {
			t.Logf("Result %d: %s", i, r)
		}
	}

	if len(results) > 0 && !strings.Contains(results[0], "active/.history: to=v2;time=") {
		t.Errorf("Unexpected result format for v2: %s", results[0])
	}
}

func TestRestoreHistoryTracking(t *testing.T) {
	tmpDir := t.TempDir()

	config := Config{
		BaseDir:           tmpDir,
		S3AccessKey:       "test",
		S3SecretAccessKey: "test",
		S3EndpointURL:     "http://localhost:9000",
		S3Bucket:          "test",
		VolumeName:        "test-volume",
	}

	jfs, err := New(config)
	if err != nil {
		t.Fatalf("Failed to create JuiceFS: %v", err)
	}

	// Simulate mount path and active directory creation
	mountPath := filepath.Join(tmpDir, "data")
	activeDir := filepath.Join(mountPath, "active")
	checkpointsDir := filepath.Join(mountPath, "checkpoints")
	if err := os.MkdirAll(activeDir, 0755); err != nil {
		t.Fatalf("Failed to create active directory: %v", err)
	}
	if err := os.MkdirAll(checkpointsDir, 0755); err != nil {
		t.Fatalf("Failed to create checkpoints directory: %v", err)
	}

	// Initialize version to v0
	versionFile := filepath.Join(activeDir, ".version")
	if err := os.WriteFile(versionFile, []byte("v0\n"), 0644); err != nil {
		t.Fatalf("Failed to write version file: %v", err)
	}

	// Simulate checkpoint creation by incrementing version
	if err := os.WriteFile(versionFile, []byte("v1\n"), 0644); err != nil {
		t.Fatalf("Failed to update version file: %v", err)
	}

	// Create a fake checkpoint v0 for restore
	v0Dir := filepath.Join(checkpointsDir, "v0")
	if err := os.MkdirAll(v0Dir, 0755); err != nil {
		t.Fatalf("Failed to create v0 directory: %v", err)
	}

	// Simulate restore: version would be incremented to v2 during pre-restore checkpoint
	if err := os.WriteFile(versionFile, []byte("v2\n"), 0644); err != nil {
		t.Fatalf("Failed to update version to v2: %v", err)
	}

	// Now append to history as if we restored
	if err := jfs.appendToHistory("v2"); err != nil {
		t.Fatalf("Failed to append to history: %v", err)
	}

	// Read history
	historyFile := filepath.Join(activeDir, ".history")
	data, err := os.ReadFile(historyFile)
	if err != nil {
		t.Fatalf("Failed to read history file: %v", err)
	}

	lines := strings.Split(strings.TrimSpace(string(data)), "\n")
	if len(lines) != 1 {
		t.Fatalf("Expected 1 history line, got %d", len(lines))
	}

	// Verify the history shows we restored TO v2 (not FROM v0)
	if !strings.HasPrefix(lines[0], "to=v2;time=") {
		t.Errorf("History should show 'to=v2', but got: %s", lines[0])
	}
}
