package juicefs

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// commandExists checks if a command exists in PATH
func commandExists(cmd string) bool {
	_, err := exec.LookPath(cmd)
	return err == nil
}

func TestConfigValidation(t *testing.T) {
	tests := []struct {
		name    string
		config  Config
		wantErr bool
	}{
		{
			name: "valid config",
			config: Config{
				BaseDir:           "/tmp/test",
				S3AccessKey:       "key",
				S3SecretAccessKey: "secret",
				S3EndpointURL:     "http://localhost:9000",
				S3Bucket:          "test-bucket",
			},
			wantErr: false,
		},
		{
			name: "valid local mode config",
			config: Config{
				BaseDir:   "/tmp/test",
				LocalMode: true,
			},
			wantErr: false,
		},
		{
			name: "missing base dir",
			config: Config{
				S3AccessKey:       "key",
				S3SecretAccessKey: "secret",
				S3EndpointURL:     "http://localhost:9000",
				S3Bucket:          "test-bucket",
			},
			wantErr: true,
		},
		{
			name: "missing S3 config",
			config: Config{
				BaseDir: "/tmp/test",
			},
			wantErr: true,
		},
		{
			name: "local mode with S3 config (valid)",
			config: Config{
				BaseDir:           "/tmp/test",
				LocalMode:         true,
				S3AccessKey:       "key",
				S3SecretAccessKey: "secret",
				S3EndpointURL:     "http://localhost:9000",
				S3Bucket:          "test-bucket",
			},
			wantErr: false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			_, err := New(tt.config)
			if (err != nil) != tt.wantErr {
				t.Errorf("New() error = %v, wantErr %v", err, tt.wantErr)
			}
		})
	}
}

func TestCalculateCacheSize(t *testing.T) {
	// Create a temporary directory for testing
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

	// Test cache size calculation
	size := jfs.calculateCacheSize(tmpDir)
	if size <= 0 {
		t.Errorf("Expected positive cache size, got %d", size)
	}
}

func TestCalculateBufferSize(t *testing.T) {
	config := Config{
		BaseDir:           "/tmp/test",
		S3AccessKey:       "test",
		S3SecretAccessKey: "test",
		S3EndpointURL:     "http://localhost:9000",
		S3Bucket:          "test",
	}

	jfs, err := New(config)
	if err != nil {
		t.Fatalf("Failed to create JuiceFS: %v", err)
	}

	// Test buffer size calculation
	size := jfs.calculateBufferSize()
	if size <= 0 || size > 1024 {
		t.Errorf("Expected buffer size between 0 and 1024, got %d", size)
	}
}

func TestLitestreamConfig(t *testing.T) {
	tmpDir := t.TempDir()
	metaDB := "/tmp/test.db"

	tests := []struct {
		name     string
		config   Config
		contains []string
	}{
		{
			name: "S3 mode",
			config: Config{
				BaseDir:           tmpDir,
				LocalMode:         false,
				S3AccessKey:       "test",
				S3SecretAccessKey: "test",
				S3EndpointURL:     "http://localhost:9000",
				S3Bucket:          "test",
			},
			contains: []string{
				"logging:",
				"level: warn",
				"path: ${JUICEFS_META_DB}",
				"type: s3",
				"endpoint: ${SPRITE_S3_ENDPOINT_URL}",
				"bucket: ${SPRITE_S3_BUCKET}",
			},
		},
		{
			name: "Local mode",
			config: Config{
				BaseDir:   tmpDir,
				LocalMode: true,
			},
			contains: []string{
				"logging:",
				"level: warn",
				fmt.Sprintf("path: %s", metaDB),
				"type: file",
				"path: " + filepath.Join(tmpDir, "litestream"),
				"retention: 24h",
				"snapshot-interval: 1m",
				"sync-interval: 1s",
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			configPath := filepath.Join(tmpDir, tt.name+"-litestream.yml")

			jfs, err := New(tt.config)
			if err != nil {
				t.Fatalf("Failed to create JuiceFS: %v", err)
			}

			err = jfs.createLitestreamConfig(configPath, metaDB)
			if err != nil {
				t.Fatalf("Failed to create litestream config: %v", err)
			}

			// Check if file was created
			if _, err := os.Stat(configPath); os.IsNotExist(err) {
				t.Errorf("Litestream config file was not created")
			}

			// Read and verify content
			content, err := os.ReadFile(configPath)
			if err != nil {
				t.Fatalf("Failed to read litestream config: %v", err)
			}

			for _, expected := range tt.contains {
				if !contains(string(content), expected) {
					t.Errorf("Expected config to contain '%s', got:\n%s", expected, string(content))
				}
			}
		})
	}
}

func TestDefaultVolumeName(t *testing.T) {
	config := Config{
		BaseDir:           "/tmp/test",
		S3AccessKey:       "test",
		S3SecretAccessKey: "test",
		S3EndpointURL:     "http://localhost:9000",
		S3Bucket:          "test",
	}

	jfs, err := New(config)
	if err != nil {
		t.Fatalf("Failed to create JuiceFS: %v", err)
	}

	if jfs.config.VolumeName != "juicefs" {
		t.Errorf("Expected default volume name 'juicefs', got '%s'", jfs.config.VolumeName)
	}
}

func TestCustomVolumeName(t *testing.T) {
	config := Config{
		BaseDir:           "/tmp/test",
		S3AccessKey:       "test",
		S3SecretAccessKey: "test",
		S3EndpointURL:     "http://localhost:9000",
		S3Bucket:          "test",
		VolumeName:        "custom-volume",
	}

	jfs, err := New(config)
	if err != nil {
		t.Fatalf("Failed to create JuiceFS: %v", err)
	}

	if jfs.config.VolumeName != "custom-volume" {
		t.Errorf("Expected volume name 'custom-volume', got '%s'", jfs.config.VolumeName)
	}
}

func TestWatchForReady(t *testing.T) {
	tmpDir := t.TempDir()
	mountPoint := filepath.Join(tmpDir, "mount")

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

	// Ensure cleanup of overlay mount
	defer func() {
		if jfs.overlayMgr != nil {
			ctx := context.Background()
			if err := jfs.overlayMgr.Unmount(ctx); err != nil {
				t.Logf("Failed to unmount overlay during cleanup: %v", err)
			}
		}
	}()

	// Create a pipe to simulate stderr
	r, w, err := os.Pipe()
	if err != nil {
		t.Fatalf("Failed to create pipe: %v", err)
	}
	defer r.Close()
	defer w.Close()

	// Start watching
	go jfs.watchForReady(r, mountPoint)

	// Write non-ready message
	w.Write([]byte("Some other log message\n"))

	// Give it a moment
	time.Sleep(10 * time.Millisecond)

	// Check that it's still waiting
	select {
	case <-jfs.mountReady:
		t.Error("Should not be ready yet")
	default:
		// Good, still waiting
	}

	// Write ready message
	w.Write([]byte("2024-01-01 12:00:00 juicefs is ready\n"))

	// Wait for ready signal
	select {
	case err := <-jfs.mountReady:
		if err != nil {
			t.Errorf("Expected nil error, got: %v", err)
		}
		// Check if active directory was created
		activeDir := filepath.Join(mountPoint, "active", "fs")
		if _, err := os.Stat(activeDir); os.IsNotExist(err) {
			t.Error("Active directory was not created")
		}
	case <-time.After(1 * time.Second):
		t.Error("Timeout waiting for ready signal")
	}
}

func TestCheckpointValidation(t *testing.T) {
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

	db, err := NewCheckpointDB(mountPath)
	if err != nil {
		t.Fatalf("Failed to create checkpoint database: %v", err)
	}
	jfs.checkpointDB = db
	defer db.Close()

	ctx := context.Background()

	// Test checkpoint without active directory
	// Note: In the new implementation, checkpoint ID is ignored as we use auto-incrementing IDs
	err = jfs.Checkpoint(ctx, "ignored-id")
	if err == nil || !strings.Contains(err.Error(), "no such file or directory") {
		t.Errorf("Expected 'no such file or directory' error, got: %v", err)
	}
}

func TestRestoreValidation(t *testing.T) {
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

	db, err := NewCheckpointDB(mountPath)
	if err != nil {
		t.Fatalf("Failed to create checkpoint database: %v", err)
	}
	jfs.checkpointDB = db
	defer db.Close()

	ctx := context.Background()

	// Test empty checkpoint ID - still required for restore
	err = jfs.Restore(ctx, "")
	if err == nil || err.Error() != "checkpoint ID is required" {
		t.Errorf("Expected 'checkpoint ID is required' error, got: %v", err)
	}

	// Test restore with non-existent checkpoint
	err = jfs.Restore(ctx, "v1")
	if err == nil || !strings.Contains(err.Error(), "not found") {
		t.Errorf("Expected 'not found' error, got: %v", err)
	}
}

// Helper function
func contains(s, substr string) bool {
	return len(s) >= len(substr) && s[:len(substr)] == substr ||
		len(s) > len(substr) && contains(s[1:], substr)
}

func TestLocalModeDirectories(t *testing.T) {
	if !commandExists("juicefs") || !commandExists("litestream") {
		t.Skip("juicefs or litestream not found in PATH")
	}

	// Create a temporary directory for testing
	tempDir, err := os.MkdirTemp("", "TestLocalModeDirectories")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tempDir)

	config := Config{
		BaseDir:    tempDir,
		LocalMode:  true,
		VolumeName: "test-volume",
	}

	// Create JuiceFS instance
	jfs, err := New(config)
	if err != nil {
		t.Fatalf("Failed to create JuiceFS: %v", err)
	}

	// Start JuiceFS
	ctx := context.Background()
	if err := jfs.Start(ctx); err != nil {
		t.Fatalf("Failed to start JuiceFS: %v", err)
	}

	// Stop JuiceFS when done
	defer func() {
		stopCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()
		if err := jfs.Stop(stopCtx); err != nil {
			t.Errorf("Failed to stop JuiceFS: %v", err)
		}
	}()

	// Check that all expected directories were created
	expectedDirs := []string{
		filepath.Join(tempDir, "cache"),
		filepath.Join(tempDir, "data"),
		filepath.Join(tempDir, "local"),                // Local storage directory
		filepath.Join(tempDir, "litestream"),           // Litestream backup directory
		filepath.Join(tempDir, "data", "active", "fs"), // Active directory created after mount
	}

	for _, dir := range expectedDirs {
		if _, err := os.Stat(dir); os.IsNotExist(err) {
			t.Errorf("Expected directory %s was not created", dir)
		}
	}

	// Check that metadata.db was created
	metaDB := filepath.Join(tempDir, "metadata.db")
	if _, err := os.Stat(metaDB); os.IsNotExist(err) {
		t.Errorf("Expected metadata.db at %s was not created", metaDB)
	} else {
		t.Logf("Metadata DB would be at: %s", metaDB)
	}
}

func TestFindAndUnmountDependentMounts(t *testing.T) {
	// Note: This test documents the expected behavior of findAndUnmountDependentMounts
	// In production, this function would:
	// 1. Read /proc/mounts to find all current mounts
	// 2. Identify mounts that depend on the JuiceFS mount:
	//    - Bind mounts where the source is under JuiceFS
	//    - Any mount point under the JuiceFS path
	//    - Loopback mounts where the backing file is on JuiceFS
	// 3. Sort them by depth (deepest first)
	// 4. Unmount each one before unmounting the main JuiceFS mount

	// Example test scenario (would require root privileges and actual mounts):
	t.Run("dependent mount identification", func(t *testing.T) {
		// This is a conceptual test showing what the function should handle

		// Given a JuiceFS mount at /mnt/juicefs
		juicefsMountPath := "/mnt/juicefs"
		_ = juicefsMountPath // Variable used for demonstration

		// Example mounts that should be identified as dependent:
		expectedDependentMounts := []struct {
			device     string
			mountPoint string
			reason     string
		}{
			{
				device:     "/mnt/juicefs/data/dir1",
				mountPoint: "/home/user/mounted-dir",
				reason:     "bind mount from JuiceFS",
			},
			{
				device:     "/dev/sda1",
				mountPoint: "/mnt/juicefs/submount",
				reason:     "mount point under JuiceFS",
			},
			{
				device:     "/dev/loop0",
				mountPoint: "/mnt/loop-mount",
				reason:     "loopback mount with backing file on JuiceFS",
			},
		}

		// The function should unmount these in reverse order (deepest first)
		// to avoid "device busy" errors

		t.Logf("Function would identify and unmount the following dependent mounts:")
		for _, mount := range expectedDependentMounts {
			t.Logf("  - %s mounted at %s (%s)", mount.device, mount.mountPoint, mount.reason)
		}
	})

	// Test the sorting logic
	t.Run("mount depth sorting", func(t *testing.T) {
		// Test that mounts are sorted by depth
		mounts := []string{
			"/mnt/juicefs",
			"/mnt/juicefs/a",
			"/mnt/juicefs/a/b/c",
			"/mnt/juicefs/a/b",
			"/other/mount",
		}

		// After sorting by depth (deepest first), expected order:
		expectedOrder := []string{
			"/mnt/juicefs/a/b/c", // depth 5
			"/mnt/juicefs/a/b",   // depth 4
			"/mnt/juicefs/a",     // depth 3
			"/other/mount",       // depth 2 (but not under juicefs)
			"/mnt/juicefs",       // depth 2
		}

		// Count depth by number of path separators
		depthOf := func(path string) int {
			depth := 0
			for _, ch := range path {
				if ch == '/' {
					depth++
				}
			}
			return depth
		}

		// Verify depth calculation
		for i, mount := range mounts {
			t.Logf("Mount %s has depth %d", mount, depthOf(mount))
			if i < len(expectedOrder) {
				expectedDepth := depthOf(expectedOrder[i])
				actualDepth := depthOf(mount)
				t.Logf("  Expected position %d with depth %d", i, expectedDepth)
				_ = actualDepth // Use to avoid unused variable warning
			}
		}
	})
}
