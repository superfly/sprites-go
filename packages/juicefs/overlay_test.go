package juicefs

import (
	"context"
	"os"
	"path/filepath"
	"testing"
)

func TestOverlayManager(t *testing.T) {
	if os.Getenv("JUICEFS_INTEGRATION_TEST") != "1" {
		t.Skip("Skipping integration test. Set JUICEFS_INTEGRATION_TEST=1 to run.")
	}

	// Create a temporary directory for testing
	tmpDir, err := os.MkdirTemp("", "juicefs-overlay-test-*")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tmpDir)

	// Create a mock JuiceFS instance
	config := Config{
		BaseDir:    tmpDir,
		LocalMode:  true,
		VolumeName: "test",
	}

	j, err := New(config)
	if err != nil {
		t.Fatalf("Failed to create JuiceFS instance: %v", err)
	}

	// Create necessary directories
	dataDir := filepath.Join(tmpDir, "data", "active")
	if err := os.MkdirAll(dataDir, 0755); err != nil {
		t.Fatalf("Failed to create data directory: %v", err)
	}

	ctx := context.Background()
	om := j.GetOverlay()

	// Test mounting
	t.Run("Mount", func(t *testing.T) {
		if err := om.Mount(ctx); err != nil {
			t.Fatalf("Failed to mount overlay: %v", err)
		}

		// Check if mount succeeded
		if !om.isMounted() {
			t.Fatal("Overlay should be mounted but isn't")
		}

		// Check if we can write to the mount
		testFile := filepath.Join(om.GetMountPath(), "test.txt")
		if err := os.WriteFile(testFile, []byte("test"), 0644); err != nil {
			t.Fatalf("Failed to write to overlay mount: %v", err)
		}

		// Clean up test file
		os.Remove(testFile)
	})

	// Test freeze/unfreeze
	t.Run("FreezeUnfreeze", func(t *testing.T) {
		if err := om.PrepareForCheckpoint(ctx); err != nil {
			t.Fatalf("Failed to prepare for checkpoint: %v", err)
		}

		// The filesystem is frozen at this point
		// We should unfreeze it
		if err := om.UnfreezeAfterCheckpoint(ctx); err != nil {
			t.Fatalf("Failed to unfreeze: %v", err)
		}

		// Check if we can write after unfreeze
		testFile := filepath.Join(om.GetMountPath(), "test2.txt")
		if err := os.WriteFile(testFile, []byte("test2"), 0644); err != nil {
			t.Fatalf("Failed to write after unfreeze: %v", err)
		}

		// Clean up test file
		os.Remove(testFile)
	})

	// Test unmounting
	t.Run("Unmount", func(t *testing.T) {
		if err := om.Unmount(ctx); err != nil {
			t.Fatalf("Failed to unmount overlay: %v", err)
		}

		// Check if unmount succeeded
		if om.isMounted() {
			t.Fatal("Overlay should be unmounted but isn't")
		}
	})

	// Test remounting
	t.Run("Remount", func(t *testing.T) {
		if err := om.Mount(ctx); err != nil {
			t.Fatalf("Failed to remount overlay: %v", err)
		}

		// Check if mount succeeded
		if !om.isMounted() {
			t.Fatal("Overlay should be mounted after remount but isn't")
		}

		// Clean up
		om.Unmount(ctx)
	})
}

func TestOverlayConfiguration(t *testing.T) {
	// Create a temporary directory for testing
	tmpDir, err := os.MkdirTemp("", "juicefs-overlay-config-test-*")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tmpDir)

	// Test with overlay configuration
	config := Config{
		BaseDir:              tmpDir,
		LocalMode:            true,
		VolumeName:           "test",
		OverlayEnabled:       true,
		OverlayImageSize:     "50G",
		OverlayLowerPath:     "/custom/lower/path",
		OverlayTargetPath:    "/custom/target/path",
		OverlaySkipOverlayFS: true,
	}

	j, err := New(config)
	if err != nil {
		t.Fatalf("Failed to create JuiceFS instance: %v", err)
	}

	om := j.GetOverlay()
	if om == nil {
		t.Fatal("Overlay manager should be created when OverlayEnabled is true")
	}

	// Test that configuration was applied
	if om.imageSize != "50G" {
		t.Errorf("Expected image size 50G, got %s", om.imageSize)
	}

	if om.GetLowerPath() != "/custom/lower/path" {
		t.Errorf("Expected lower path /custom/lower/path, got %s", om.GetLowerPath())
	}

	if om.GetOverlayTargetPath() != "/custom/target/path" {
		t.Errorf("Expected target path /custom/target/path, got %s", om.GetOverlayTargetPath())
	}

	if !om.skipOverlayFS {
		t.Error("Expected skipOverlayFS to be true")
	}

	// Test backward compatibility methods
	om.SetAppImagePath("/new/app/path")
	if om.GetLowerPath() != "/new/app/path" {
		t.Errorf("SetAppImagePath should update lower path, got %s", om.GetLowerPath())
	}

	if om.GetAppImagePath() != "/new/app/path" {
		t.Errorf("GetAppImagePath should return lower path, got %s", om.GetAppImagePath())
	}
}

func TestOverlayDisabled(t *testing.T) {
	// Create a temporary directory for testing
	tmpDir, err := os.MkdirTemp("", "juicefs-overlay-disabled-test-*")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tmpDir)

	// Test with overlay disabled
	config := Config{
		BaseDir:        tmpDir,
		LocalMode:      true,
		VolumeName:     "test",
		OverlayEnabled: false, // Explicitly disabled
	}

	j, err := New(config)
	if err != nil {
		t.Fatalf("Failed to create JuiceFS instance: %v", err)
	}

	om := j.GetOverlay()
	if om != nil {
		t.Fatal("Overlay manager should not be created when OverlayEnabled is false")
	}
}
