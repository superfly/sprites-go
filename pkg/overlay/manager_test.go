package overlay

import (
	"context"
	"os"
	"testing"
)

func TestManagerConfig(t *testing.T) {
	// Test configuration defaults
	cfg := Config{
		BaseDir: "/tmp/test",
	}
	m := New(cfg)

	if m.imageSize != "100G" {
		t.Errorf("expected default image size 100G, got %s", m.imageSize)
	}
	if m.mountPath != "/mnt/user-data" {
		t.Errorf("expected default mount path /mnt/user-data, got %s", m.mountPath)
	}
	if m.overlayTargetPath != "/mnt/newroot" {
		t.Errorf("expected default overlay target /mnt/newroot, got %s", m.overlayTargetPath)
	}
	if len(m.lowerPaths) != 1 || m.lowerPaths[0] != "/mnt/system-base" {
		t.Errorf("expected default lower paths [/mnt/system-base], got %v", m.lowerPaths)
	}
}

func TestManagerLinuxOnly(t *testing.T) {
	// Overlay tests always run in Linux Docker environment

	// Check if overlayfs is available
	if _, err := os.Stat("/sys/module/overlay"); os.IsNotExist(err) {
		t.Fatal("Overlay tests require overlayfs support in kernel")
	}

	ctx := context.Background()
	cfg := Config{
		BaseDir:       t.TempDir(),
		SkipOverlayFS: true, // Skip overlayfs for basic tests
	}
	m := New(cfg)

	// Test that we can't mount without root
	if os.Getuid() != 0 {
		t.Log("Running as non-root, mount operations will fail")
		if err := m.Mount(ctx); err == nil {
			t.Fatal("expected mount to fail as non-root")
		}
		return
	}

	// If we're root, test basic mount/unmount
	defer VerifyNoTestOverlays(t, m)

	t.Run("Mount", func(t *testing.T) {
		// Ensure image exists before mounting
		if err := m.EnsureImage(); err != nil {
			t.Fatalf("failed to ensure image: %v", err)
		}
		if err := m.Mount(ctx); err != nil {
			t.Fatalf("failed to mount: %v", err)
		}
		if !m.isMounted() {
			t.Fatal("expected to be mounted")
		}
	})

	t.Run("Unmount", func(t *testing.T) {
		if err := m.Unmount(ctx); err != nil {
			t.Fatalf("failed to unmount: %v", err)
		}
		if m.isMounted() {
			t.Fatal("expected to be unmounted")
		}
	})
}

func TestPrepareCheckpointLinuxOnly(t *testing.T) {
	// Overlay tests always run as root in Linux Docker environment

	ctx := context.Background()
	cfg := Config{
		BaseDir:       t.TempDir(),
		SkipOverlayFS: true,
	}
	m := New(cfg)
	defer VerifyNoTestOverlays(t, m)

	// Ensure image exists before mounting
	if err := m.EnsureImage(); err != nil {
		t.Fatalf("failed to ensure image: %v", err)
	}

	// Mount first
	if err := m.Mount(ctx); err != nil {
		t.Fatalf("failed to mount: %v", err)
	}

	// Test sync functionality
	if err := m.PrepareForCheckpoint(ctx); err != nil {
		t.Fatalf("failed to sync: %v", err)
	}

	// Cleanup
	if err := m.Unmount(ctx); err != nil {
		t.Fatalf("failed to unmount: %v", err)
	}
}
