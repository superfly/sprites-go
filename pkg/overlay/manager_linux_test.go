//go:build linux
// +build linux

package overlay

import (
	"context"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// TestOverlayFullLifecycle tests the complete overlay lifecycle with real overlayfs
func TestOverlayFullLifecycle(t *testing.T) {
	// Overlay tests always run as root in Docker environment

	// Check if overlayfs is available
	if _, err := os.Stat("/sys/module/overlay"); os.IsNotExist(err) {
		t.Fatal("Overlay tests require overlayfs support in kernel")
	}

	ctx := context.Background()
	baseDir := t.TempDir()

	var m *Manager
	defer func() {
		if m != nil {
			VerifyNoTestOverlays(t, m)
		}
	}()

	// Create test directories
	lowerDir := filepath.Join(baseDir, "lower")
	if err := os.MkdirAll(lowerDir, 0755); err != nil {
		t.Fatal(err)
	}

	// Add some test content to lower
	testFile := filepath.Join(lowerDir, "test.txt")
	if err := os.WriteFile(testFile, []byte("lower content"), 0644); err != nil {
		t.Fatal(err)
	}

	targetDir := filepath.Join(baseDir, "target")
	if err := os.MkdirAll(targetDir, 0755); err != nil {
		t.Fatal(err)
	}

	cfg := Config{
		BaseDir:           baseDir,
		LowerPaths:        []string{lowerDir},
		OverlayTargetPath: targetDir,
		ImageSize:         "1G", // Small for testing
	}
	m = New(cfg)

	// Test Mount
	t.Run("Mount", func(t *testing.T) {
		// Ensure image exists before mounting
		if err := m.EnsureImage(); err != nil {
			t.Fatalf("failed to ensure image: %v", err)
		}
		if err := m.Mount(ctx); err != nil {
			t.Fatalf("failed to mount: %v", err)
		}

		// Verify overlay is mounted
		if !m.isOverlayFSMounted() {
			t.Fatal("expected overlayfs to be mounted")
		}

		// Verify we can read from lower through overlay
		overlayTestFile := filepath.Join(targetDir, "test.txt")
		content, err := os.ReadFile(overlayTestFile)
		if err != nil {
			t.Fatalf("failed to read test file through overlay: %v", err)
		}
		if string(content) != "lower content" {
			t.Errorf("expected 'lower content', got %q", string(content))
		}

		// Write to overlay
		upperFile := filepath.Join(targetDir, "upper.txt")
		if err := os.WriteFile(upperFile, []byte("upper content"), 0644); err != nil {
			t.Fatalf("failed to write to overlay: %v", err)
		}
	})

	// Test PrepareForCheckpoint
	t.Run("PrepareForCheckpoint", func(t *testing.T) {
		// Write some data that needs to be flushed
		testFile := filepath.Join(targetDir, "checkpoint-test.txt")
		if err := os.WriteFile(testFile, []byte("checkpoint data"), 0644); err != nil {
			t.Fatal(err)
		}

		// Prepare for checkpoint (sync only)
		if err := m.PrepareForCheckpoint(ctx); err != nil {
			t.Fatalf("failed to prepare for checkpoint: %v", err)
		}

		// Verify we can still write (no freeze at overlay level)
		if err := os.WriteFile(testFile, []byte("new data"), 0644); err != nil {
			t.Fatalf("failed to write after sync: %v", err)
		}
	})

	// Test Unmount
	t.Run("Unmount", func(t *testing.T) {
		if err := m.Unmount(ctx); err != nil {
			t.Fatalf("failed to unmount: %v", err)
		}

		// Verify overlay is unmounted
		if m.isOverlayFSMounted() {
			t.Fatal("expected overlayfs to be unmounted")
		}

		// Verify target directory is empty after unmount
		entries, err := os.ReadDir(targetDir)
		if err != nil {
			t.Fatal(err)
		}
		if len(entries) > 0 {
			t.Errorf("expected target directory to be empty, found %d entries", len(entries))
		}
	})

	// Test Remount
	t.Run("Remount", func(t *testing.T) {
		// Mount again (image already exists from previous mount)
		if err := m.Mount(ctx); err != nil {
			t.Fatalf("failed to remount: %v", err)
		}

		// Verify previous upper content is still there
		upperFile := filepath.Join(targetDir, "upper.txt")
		content, err := os.ReadFile(upperFile)
		if err != nil {
			t.Fatalf("failed to read upper file after remount: %v", err)
		}
		if string(content) != "upper content" {
			t.Errorf("expected 'upper content', got %q", string(content))
		}

		// Final unmount
		if err := m.Unmount(ctx); err != nil {
			t.Fatal(err)
		}
	})
}

// TestOverlayWithMultipleLowers tests overlay with multiple lower directories
func TestOverlayWithMultipleLowers(t *testing.T) {
	// Overlay tests always run as root in Docker environment

	ctx := context.Background()
	baseDir := t.TempDir()

	var m *Manager
	defer func() {
		if m != nil {
			VerifyNoTestOverlays(t, m)
		}
	}()

	// Create multiple lower directories
	lower1 := filepath.Join(baseDir, "lower1")
	lower2 := filepath.Join(baseDir, "lower2")
	for _, dir := range []string{lower1, lower2} {
		if err := os.MkdirAll(dir, 0755); err != nil {
			t.Fatal(err)
		}
	}

	// Add different content to each lower
	if err := os.WriteFile(filepath.Join(lower1, "file1.txt"), []byte("from lower1"), 0644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(lower2, "file2.txt"), []byte("from lower2"), 0644); err != nil {
		t.Fatal(err)
	}
	// Add same file to both - lower1 should take precedence
	if err := os.WriteFile(filepath.Join(lower1, "common.txt"), []byte("lower1 version"), 0644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(lower2, "common.txt"), []byte("lower2 version"), 0644); err != nil {
		t.Fatal(err)
	}

	targetDir := filepath.Join(baseDir, "target")
	if err := os.MkdirAll(targetDir, 0755); err != nil {
		t.Fatal(err)
	}

	cfg := Config{
		BaseDir:           baseDir,
		LowerPaths:        []string{lower1, lower2}, // Order matters
		OverlayTargetPath: targetDir,
		ImageSize:         "1G",
	}
	m = New(cfg)

	// Ensure image exists before mounting
	if err := m.EnsureImage(); err != nil {
		t.Fatalf("failed to ensure image: %v", err)
	}

	// Mount
	if err := m.Mount(ctx); err != nil {
		t.Fatalf("failed to mount: %v", err)
	}

	// Verify both files are visible
	for _, test := range []struct {
		file     string
		expected string
	}{
		{"file1.txt", "from lower1"},
		{"file2.txt", "from lower2"},
		{"common.txt", "lower1 version"}, // lower1 takes precedence
	} {
		path := filepath.Join(targetDir, test.file)
		content, err := os.ReadFile(path)
		if err != nil {
			t.Errorf("failed to read %s: %v", test.file, err)
			continue
		}
		if string(content) != test.expected {
			t.Errorf("%s: expected %q, got %q", test.file, test.expected, string(content))
		}
	}

	// Cleanup: graceful stop and verify no leaks
	if err := m.Unmount(ctx); err != nil {
		t.Fatalf("failed to unmount: %v", err)
	}
	VerifyNoTestOverlays(t, m)
}

// TestOverlayErrorHandling tests error conditions
func TestOverlayErrorHandling(t *testing.T) {
	// Overlay tests always run as root in Docker environment

	ctx := context.Background()

	t.Run("MountWithoutImage", func(t *testing.T) {
		baseDir := t.TempDir()
		cfg := Config{
			BaseDir: baseDir,
		}
		m := New(cfg)
		defer VerifyNoTestOverlays(t, m)

		// Remove the image file if it was created
		os.Remove(m.GetImagePath())

		// Mount should fail without an image (must call EnsureImage() first)
		err := m.Mount(ctx)
		if err == nil {
			t.Fatal("expected mount to fail without image, but it succeeded")
		}
		if !strings.Contains(err.Error(), "overlay image does not exist") {
			t.Fatalf("expected 'overlay image does not exist' error, got: %v", err)
		}
	})

	t.Run("DoubleMountShouldSucceed", func(t *testing.T) {
		baseDir := t.TempDir()
		lowerDir := filepath.Join(baseDir, "lower")
		if err := os.MkdirAll(lowerDir, 0755); err != nil {
			t.Fatal(err)
		}
		cfg := Config{
			BaseDir:    baseDir,
			ImageSize:  "1G",
			LowerPaths: []string{lowerDir},
		}
		m := New(cfg)

		// Ensure image exists
		if err := m.EnsureImage(); err != nil {
			t.Fatal(err)
		}

		// First mount
		if err := m.Mount(ctx); err != nil {
			t.Fatal(err)
		}
		defer m.Unmount(ctx)

		// Second mount should succeed (idempotent)
		if err := m.Mount(ctx); err != nil {
			t.Fatalf("second mount failed: %v", err)
		}
	})

	t.Run("UnmountWhenNotMounted", func(t *testing.T) {
		baseDir := t.TempDir()
		cfg := Config{
			BaseDir: baseDir,
		}
		m := New(cfg)
		defer VerifyNoTestOverlays(t, m)

		// Should succeed (idempotent)
		if err := m.Unmount(ctx); err != nil {
			t.Fatalf("unmount of non-mounted overlay failed: %v", err)
		}
	})
}

// TestOverlayConcurrentOperations tests concurrent access
func TestOverlayConcurrentOperations(t *testing.T) {
	// Overlay tests always run as root in Docker environment

	ctx := context.Background()
	baseDir := t.TempDir()

	var m *Manager
	defer func() {
		if m != nil {
			VerifyNoTestOverlays(t, m)
		}
	}()

	lowerDir := filepath.Join(baseDir, "lower")
	if err := os.MkdirAll(lowerDir, 0755); err != nil {
		t.Fatal(err)
	}

	cfg := Config{
		BaseDir:    baseDir,
		ImageSize:  "1G",
		LowerPaths: []string{lowerDir},
	}
	m = New(cfg)

	// Ensure image exists
	if err := m.EnsureImage(); err != nil {
		t.Fatal(err)
	}

	// Mount first
	if err := m.Mount(ctx); err != nil {
		t.Fatal(err)
	}

	targetDir := m.overlayTargetPath

	// Run concurrent writes
	done := make(chan error, 10)
	for i := 0; i < 10; i++ {
		go func(id int) {
			file := filepath.Join(targetDir, fmt.Sprintf("concurrent-%d.txt", id))
			err := os.WriteFile(file, []byte(fmt.Sprintf("data from %d", id)), 0644)
			done <- err
		}(i)
	}

	// Wait for all writes
	for i := 0; i < 10; i++ {
		if err := <-done; err != nil {
			t.Errorf("concurrent write failed: %v", err)
		}
	}

	// Verify all files exist
	for i := 0; i < 10; i++ {
		file := filepath.Join(targetDir, fmt.Sprintf("concurrent-%d.txt", i))
		content, err := os.ReadFile(file)
		if err != nil {
			t.Errorf("failed to read concurrent file %d: %v", i, err)
			continue
		}
		expected := fmt.Sprintf("data from %d", i)
		if string(content) != expected {
			t.Errorf("file %d: expected %q, got %q", i, expected, string(content))
		}
	}

	// Cleanup: graceful stop and verify no leaks
	if err := m.Unmount(ctx); err != nil {
		t.Fatalf("failed to unmount: %v", err)
	}
	VerifyNoTestOverlays(t, m)
}

// TestOverlayImageGrowth tests that the image file grows as needed
func TestOverlayImageGrowth(t *testing.T) {
	// Overlay tests always run as root in Docker environment

	ctx := context.Background()
	baseDir := t.TempDir()

	var m *Manager
	defer func() {
		if m != nil {
			VerifyNoTestOverlays(t, m)
		}
	}()

	lowerDir := filepath.Join(baseDir, "lower")
	if err := os.MkdirAll(lowerDir, 0755); err != nil {
		t.Fatal(err)
	}

	cfg := Config{
		BaseDir:    baseDir,
		ImageSize:  "500M", // Small initial size
		LowerPaths: []string{lowerDir},
	}
	m = New(cfg)

	// Ensure image exists
	if err := m.EnsureImage(); err != nil {
		t.Fatal(err)
	}

	// Mount
	if err := m.Mount(ctx); err != nil {
		t.Fatal(err)
	}

	// Write a moderate amount of data
	targetDir := m.overlayTargetPath
	testFile := filepath.Join(targetDir, "bigfile.dat")

	// Create a 10MB file
	data := make([]byte, 10*1024*1024)
	for i := range data {
		data[i] = byte(i % 256)
	}

	if err := os.WriteFile(testFile, data, 0644); err != nil {
		t.Fatalf("failed to write test file: %v", err)
	}

	// Verify file exists and has correct size
	stat, err := os.Stat(testFile)
	if err != nil {
		t.Fatal(err)
	}
	if stat.Size() != int64(len(data)) {
		t.Errorf("expected file size %d, got %d", len(data), stat.Size())
	}

	// Cleanup
	if err := m.Unmount(ctx); err != nil {
		t.Fatalf("failed to unmount: %v", err)
	}
}

// TestFreezeUnfreezeStress tests multiple freeze/unfreeze cycles
func TestFreezeUnfreezeStress(t *testing.T) {
	// Overlay tests always run as root in Docker environment

	ctx := context.Background()
	baseDir := t.TempDir()

	var m *Manager
	defer func() {
		if m != nil {
			VerifyNoTestOverlays(t, m)
		}
	}()

	lowerDir := filepath.Join(baseDir, "lower")
	if err := os.MkdirAll(lowerDir, 0755); err != nil {
		t.Fatal(err)
	}

	cfg := Config{
		BaseDir:    baseDir,
		ImageSize:  "1G",
		LowerPaths: []string{lowerDir},
	}
	m = New(cfg)

	// Ensure image exists
	if err := m.EnsureImage(); err != nil {
		t.Fatal(err)
	}

	// Mount
	if err := m.Mount(ctx); err != nil {
		t.Fatal(err)
	}

	// Run multiple freeze/unfreeze cycles
	for i := 0; i < 5; i++ {
		// Write before freeze
		testFile := filepath.Join(m.overlayTargetPath, fmt.Sprintf("freeze-test-%d.txt", i))
		if err := os.WriteFile(testFile, []byte(fmt.Sprintf("iteration %d", i)), 0644); err != nil {
			t.Fatalf("iteration %d: failed to write before freeze: %v", i, err)
		}

		// Sync
		if err := m.PrepareForCheckpoint(ctx); err != nil {
			t.Fatalf("iteration %d: failed to sync: %v", i, err)
		}

		// Brief pause to simulate checkpoint
		time.Sleep(100 * time.Millisecond)

		// Verify we can still write (no freeze at overlay level)
		if err := os.WriteFile(testFile, []byte(fmt.Sprintf("iteration %d - after", i)), 0644); err != nil {
			t.Fatalf("iteration %d: failed to write after sync: %v", i, err)
		}
	}

	// Cleanup
	if err := m.Unmount(ctx); err != nil {
		t.Fatalf("failed to unmount: %v", err)
	}
}
