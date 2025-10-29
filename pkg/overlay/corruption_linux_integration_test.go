//go:build linux

package overlay

import (
	"context"
	"errors"
	"os"
	"path/filepath"
	"strings"
	"sync/atomic"
	"testing"
)

// This integration test verifies corruption recovery path by injecting an I/O error
// on the first mountExt4 call, then ensuring the image is backed up and remounted.
func TestCorruptionRecovery_BackupAndRemount(t *testing.T) {
	if os.Geteuid() != 0 {
		t.Skip("requires root")
	}

	baseDir := t.TempDir()
	mountPath := filepath.Join(baseDir, "mnt")
	lower := filepath.Join(baseDir, "lower")
	if err := os.MkdirAll(lower, 0755); err != nil {
		t.Fatal(err)
	}

	mCfg := Config{BaseDir: baseDir, ImageSize: "10G", MountPath: mountPath, LowerPaths: []string{lower}}
	m := New(mCfg)

	// Ensure initial image exists
	if err := m.EnsureImage(); err != nil {
		t.Fatalf("ensure image: %v", err)
	}
	img := m.GetImagePath()

	// Inject single failure on mountExt4
	var called int32
	orig := mountExt4Func
	t.Cleanup(func() { mountExt4Func = orig })
	mountExt4Func = func(device, target, options string) error {
		if atomic.AddInt32(&called, 1) == 1 {
			return errors.New("input/output error: simulated")
		}
		return orig(device, target, options)
	}

	ctx := context.Background()
	if err := m.PrepareAndMount(ctx); err != nil {
		t.Fatalf("PrepareAndMount: %v", err)
	}

	// Verify new image exists and a .bak was created
	if _, err := os.Stat(m.GetImagePath()); err != nil {
		t.Fatalf("new image missing: %v", err)
	}
	matches, _ := filepath.Glob(strings.TrimSuffix(img, ".img") + ".corrupt-*.bak")
	if len(matches) == 0 {
		t.Fatalf("expected .bak backup to be created")
	}

	_ = m.Unmount(ctx)
}
