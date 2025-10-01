package overlay

import (
	"context"
	"os"
	"runtime"
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
	if runtime.GOOS != "linux" {
		t.Skip("Overlay tests require Linux")
	}

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
	t.Run("Mount", func(t *testing.T) {
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
	if runtime.GOOS != "linux" {
		t.Skip("Overlay tests require Linux")
	}
	if os.Getuid() != 0 {
		t.Skip("Overlay tests require root")
	}

	ctx := context.Background()
	cfg := Config{
		BaseDir:       t.TempDir(),
		SkipOverlayFS: true,
	}
	m := New(cfg)

	// Mount first
	if err := m.Mount(ctx); err != nil {
		t.Fatalf("failed to mount: %v", err)
	}
	defer m.Unmount(ctx)

	// Test freeze/unfreeze
	if err := m.PrepareForCheckpoint(ctx); err != nil {
		t.Fatalf("failed to prepare: %v", err)
	}

	// Should be frozen now
	if err := m.UnfreezeAfterCheckpoint(ctx); err != nil {
		t.Fatalf("failed to unfreeze: %v", err)
	}
}
