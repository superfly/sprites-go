package juicefs

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

func TestWhenReady(t *testing.T) {
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

	// Start watching - simulate the new parseLogsForReady behavior
	go func() {
		ticker := time.NewTicker(100 * time.Millisecond)
		defer ticker.Stop()

		timeout := time.After(2 * time.Minute)
		for {
			select {
			case <-ticker.C:
				if jfs.isMountReady(mountPoint) {
					close(jfs.mountReady)
					return
				}
			case <-timeout:
				jfs.mountErrorMu.Lock()
				jfs.mountError = fmt.Errorf("timeout waiting for mount")
				jfs.mountErrorMu.Unlock()
				close(jfs.mountReady)
				return
			}
		}
	}()

	// Give it a moment to start polling
	time.Sleep(50 * time.Millisecond)

	// Check that it's still waiting (mount point doesn't exist yet so it should timeout)
	ctx, cancel := context.WithTimeout(context.Background(), 200*time.Millisecond)
	defer cancel()

	err = jfs.WhenReady(ctx)
	if err == nil {
		t.Error("Should have received timeout error since no real mount exists")
	} else if err != context.DeadlineExceeded {
		// The context should timeout before the mount is ready
		t.Errorf("Expected context deadline exceeded, got: %v", err)
	} else {
		// This is expected - it should still be polling
		t.Log("WhenReady is still waiting as expected")
	}
}

func TestQuotaApplication(t *testing.T) {
	// This test requires the Docker test environment
	if os.Getenv("SPRITE_TEST_DOCKER") != "1" {
		t.Fatal("This test must run in the Docker test environment (SPRITE_TEST_DOCKER=1)")
	}

	// In Docker, these tools must be present - fail if they're not
	if !commandExists("juicefs") {
		t.Fatal("juicefs not found in PATH - Docker test environment is misconfigured")
	}
	if !commandExists("litestream") {
		t.Fatal("litestream not found in PATH - Docker test environment is misconfigured")
	}

	// Create a temporary directory for testing
	tempDir, err := os.MkdirTemp("", "TestQuotaApplication")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tempDir)

	// Create a logger for detailed output
	logger := slog.New(slog.NewTextHandler(os.Stderr, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))

	config := Config{
		BaseDir:    tempDir,
		LocalMode:  true,
		VolumeName: "test-quota-volume",
		Logger:     logger,
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
	defer func() {
		// Stop JuiceFS - in Docker environment this should work reliably
		// Use a generous timeout for data integrity
		stopCtx, cancel := context.WithTimeout(context.Background(), 5*time.Minute)
		defer cancel()
		if err := jfs.Stop(stopCtx); err != nil {
			t.Errorf("Failed to stop JuiceFS: %v", err)
		}
	}()

	// Give quota application time to run
	time.Sleep(5 * time.Second)

	// Check quota using juicefs quota get command
	metaDB := filepath.Join(tempDir, "metadata.db")
	metaURL := fmt.Sprintf("sqlite3://%s", metaDB)

	quotaCmd := exec.Command("juicefs", "quota", "get", metaURL, "--path", "/active/fs")
	output, err := quotaCmd.CombinedOutput()

	if err != nil {
		t.Logf("Quota check output: %s", string(output))
		t.Fatalf("Failed to get quota: %v", err)
	}

	// Check if output contains 10TB quota
	outputStr := string(output)
	if strings.Contains(outputStr, "10 TiB") || strings.Contains(outputStr, "10240 GiB") {
		t.Logf("Successfully verified 10TB quota on /active/fs")
	} else {
		t.Logf("Quota output: %s", outputStr)
		t.Errorf("Expected 10TB quota not found in output")
	}
}

func TestFindDependentMounts(t *testing.T) {
	// Note: This test documents the expected behavior of findDependentMounts
	// In production, this function:
	// 1. Reads /proc/mounts to find all current mounts
	// 2. Identifies mounts that depend on the JuiceFS mount:
	//    - Bind mounts where the source is under JuiceFS
	//    - Any mount point under the JuiceFS path
	//    - Loopback mounts where the backing file is on JuiceFS
	// 3. Returns the list (does NOT unmount them)
	// 4. JuiceFS Stop() will fail if dependent mounts exist

	// Example test scenario (would require root privileges and actual mounts):
	t.Run("dependent mount identification", func(t *testing.T) {
		// This is a conceptual test showing what the function should detect

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

		// The function should identify these and Stop() should fail with error:
		// "cannot stop JuiceFS, there are N mount(s) relying on it"

		t.Logf("Function would identify the following dependent mounts:")
		for _, mount := range expectedDependentMounts {
			t.Logf("  - %s mounted at %s (%s)", mount.device, mount.mountPoint, mount.reason)
		}
		t.Logf("JuiceFS Stop() would fail if these mounts exist")
	})
}
