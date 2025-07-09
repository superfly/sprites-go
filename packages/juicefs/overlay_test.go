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

func TestOverlayMultipleLowerPaths(t *testing.T) {
	// Create a temporary directory for testing
	tmpDir, err := os.MkdirTemp("", "juicefs-overlay-multiple-lower-test-*")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tmpDir)

	// Test with multiple lower paths
	config := Config{
		BaseDir:              tmpDir,
		LocalMode:            true,
		VolumeName:           "test",
		OverlayEnabled:       true,
		OverlayImageSize:     "50G",
		OverlayLowerPaths:    []string{"/first/lower", "/second/lower", "/third/lower"},
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

	// Test that multiple lower paths were applied
	lowerPaths := om.GetLowerPaths()
	expected := []string{"/first/lower", "/second/lower", "/third/lower"}
	if len(lowerPaths) != len(expected) {
		t.Errorf("Expected %d lower paths, got %d", len(expected), len(lowerPaths))
	}

	for i, path := range expected {
		if i >= len(lowerPaths) || lowerPaths[i] != path {
			t.Errorf("Expected lower path %d to be %s, got %s", i, path, lowerPaths[i])
		}
	}

	// Test backward compatibility - GetLowerPath should return first path
	if om.GetLowerPath() != "/first/lower" {
		t.Errorf("GetLowerPath should return first lower path, got %s", om.GetLowerPath())
	}

	// Test setting multiple paths
	newPaths := []string{"/new/first", "/new/second"}
	om.SetLowerPaths(newPaths)

	updatedPaths := om.GetLowerPaths()
	if len(updatedPaths) != len(newPaths) {
		t.Errorf("Expected %d lower paths after SetLowerPaths, got %d", len(newPaths), len(updatedPaths))
	}

	for i, path := range newPaths {
		if i >= len(updatedPaths) || updatedPaths[i] != path {
			t.Errorf("Expected updated lower path %d to be %s, got %s", i, path, updatedPaths[i])
		}
	}
}

func TestOverlayBackwardCompatibility(t *testing.T) {
	// Create a temporary directory for testing
	tmpDir, err := os.MkdirTemp("", "juicefs-overlay-backward-compat-test-*")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tmpDir)

	// Test with single lower path (backward compatibility)
	config := Config{
		BaseDir:              tmpDir,
		LocalMode:            true,
		VolumeName:           "test",
		OverlayEnabled:       true,
		OverlayImageSize:     "50G",
		OverlayLowerPath:     "/single/lower/path",
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

	// Test that single lower path was converted to array
	lowerPaths := om.GetLowerPaths()
	if len(lowerPaths) != 1 {
		t.Errorf("Expected 1 lower path, got %d", len(lowerPaths))
	}

	if lowerPaths[0] != "/single/lower/path" {
		t.Errorf("Expected lower path to be /single/lower/path, got %s", lowerPaths[0])
	}

	// Test backward compatibility methods
	if om.GetLowerPath() != "/single/lower/path" {
		t.Errorf("GetLowerPath should return single lower path, got %s", om.GetLowerPath())
	}

	// Test SetLowerPath (deprecated method)
	om.SetLowerPath("/new/single/path")
	if om.GetLowerPath() != "/new/single/path" {
		t.Errorf("SetLowerPath should update lower path, got %s", om.GetLowerPath())
	}

	// Should now have only one path in the array
	updatedPaths := om.GetLowerPaths()
	if len(updatedPaths) != 1 || updatedPaths[0] != "/new/single/path" {
		t.Errorf("Expected single path array [/new/single/path], got %v", updatedPaths)
	}
}

func TestOverlayPriorityAndFallback(t *testing.T) {
	// Create a temporary directory for testing
	tmpDir, err := os.MkdirTemp("", "juicefs-overlay-priority-test-*")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tmpDir)

	// Test priority: OverlayLowerPaths takes precedence over OverlayLowerPath
	config := Config{
		BaseDir:              tmpDir,
		LocalMode:            true,
		VolumeName:           "test",
		OverlayEnabled:       true,
		OverlayImageSize:     "50G",
		OverlayLowerPath:     "/should/be/ignored",
		OverlayLowerPaths:    []string{"/first/priority", "/second/priority"},
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

	// Test that OverlayLowerPaths was used, not OverlayLowerPath
	lowerPaths := om.GetLowerPaths()
	expected := []string{"/first/priority", "/second/priority"}
	if len(lowerPaths) != len(expected) {
		t.Errorf("Expected %d lower paths, got %d", len(expected), len(lowerPaths))
	}

	for i, path := range expected {
		if i >= len(lowerPaths) || lowerPaths[i] != path {
			t.Errorf("Expected lower path %d to be %s, got %s", i, path, lowerPaths[i])
		}
	}

	// Test fallback to default when neither is set
	configDefault := Config{
		BaseDir:              tmpDir,
		LocalMode:            true,
		VolumeName:           "test",
		OverlayEnabled:       true,
		OverlayImageSize:     "50G",
		OverlayTargetPath:    "/custom/target/path",
		OverlaySkipOverlayFS: true,
	}

	j2, err := New(configDefault)
	if err != nil {
		t.Fatalf("Failed to create JuiceFS instance with default config: %v", err)
	}

	om2 := j2.GetOverlay()
	if om2 == nil {
		t.Fatal("Overlay manager should be created when OverlayEnabled is true")
	}

	// Test that default lower path was used
	defaultPaths := om2.GetLowerPaths()
	if len(defaultPaths) != 1 || defaultPaths[0] != "/mnt/app-image" {
		t.Errorf("Expected default lower path [/mnt/app-image], got %v", defaultPaths)
	}
}

func TestOverlayMountOptionsGeneration(t *testing.T) {
	// Create a temporary directory for testing
	tmpDir, err := os.MkdirTemp("", "juicefs-overlay-mount-options-test-*")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tmpDir)

	// Test that mount options are generated correctly with multiple paths
	config := Config{
		BaseDir:              tmpDir,
		LocalMode:            true,
		VolumeName:           "test",
		OverlayEnabled:       true,
		OverlayImageSize:     "50G",
		OverlayLowerPaths:    []string{"/path1", "/path2", "/path3"},
		OverlayTargetPath:    "/custom/target/path",
		OverlaySkipOverlayFS: false, // Enable overlayfs to test mount options
	}

	j, err := New(config)
	if err != nil {
		t.Fatalf("Failed to create JuiceFS instance: %v", err)
	}

	om := j.GetOverlay()
	if om == nil {
		t.Fatal("Overlay manager should be created when OverlayEnabled is true")
	}

	// Test that paths are properly stored
	lowerPaths := om.GetLowerPaths()
	expected := []string{"/path1", "/path2", "/path3"}
	if len(lowerPaths) != len(expected) {
		t.Errorf("Expected %d lower paths, got %d", len(expected), len(lowerPaths))
	}

	for i, path := range expected {
		if i >= len(lowerPaths) || lowerPaths[i] != path {
			t.Errorf("Expected lower path %d to be %s, got %s", i, path, lowerPaths[i])
		}
	}

	// Note: We can't test the actual mount command without creating real directories
	// and running as root, but we can verify the paths are stored correctly
}

func TestOverlayEmptyLowerPaths(t *testing.T) {
	// Create a temporary directory for testing
	tmpDir, err := os.MkdirTemp("", "juicefs-overlay-empty-test-*")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tmpDir)

	// Test with empty lower paths array
	config := Config{
		BaseDir:              tmpDir,
		LocalMode:            true,
		VolumeName:           "test",
		OverlayEnabled:       true,
		OverlayImageSize:     "50G",
		OverlayLowerPaths:    []string{}, // Empty array
		OverlayLowerPath:     "/fallback/path",
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

	// Test that it falls back to single path when array is empty
	lowerPaths := om.GetLowerPaths()
	if len(lowerPaths) != 1 || lowerPaths[0] != "/fallback/path" {
		t.Errorf("Expected fallback to single path [/fallback/path], got %v", lowerPaths)
	}
}

func TestOverlayGetLowerPathEmptyArray(t *testing.T) {
	// Create a temporary directory for testing
	tmpDir, err := os.MkdirTemp("", "juicefs-overlay-empty-array-test-*")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tmpDir)

	// Test with completely empty configuration
	config := Config{
		BaseDir:              tmpDir,
		LocalMode:            true,
		VolumeName:           "test",
		OverlayEnabled:       true,
		OverlayImageSize:     "50G",
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

	// Manually clear the lower paths to test empty array behavior
	om.SetLowerPaths([]string{})

	// GetLowerPath should return empty string for empty array
	if om.GetLowerPath() != "" {
		t.Errorf("GetLowerPath should return empty string for empty array, got %s", om.GetLowerPath())
	}

	// GetLowerPaths should return empty array
	if len(om.GetLowerPaths()) != 0 {
		t.Errorf("GetLowerPaths should return empty array, got %v", om.GetLowerPaths())
	}
}
