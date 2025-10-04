package tests

import (
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"testing"
	"time"
)

func logTS(t *testing.T, msg string) {
	t.Helper()
	t.Logf("%s %s", time.Now().Format(time.RFC3339Nano), msg)
}

func dumpCmd(t *testing.T, name string, args ...string) {
	t.Helper()
	ctx, cancel := context.WithTimeout(context.Background(), 3*time.Second)
	defer cancel()
	cmd := exec.CommandContext(ctx, name, args...)
	out, err := cmd.CombinedOutput()
	if ctx.Err() == context.DeadlineExceeded {
		t.Logf("%s %s timed out after 3s", time.Now().Format(time.RFC3339Nano), name)
		return
	}
	if err != nil {
		t.Logf("%s %s error: %v", time.Now().Format(time.RFC3339Nano), name, err)
	}
	t.Logf("%s %s\n%s", time.Now().Format(time.RFC3339Nano), name, string(out))
}

func mountOutput(t *testing.T) string {
	cmd := exec.Command("mount")
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("failed to run mount: %v", err)
	}
	return string(out)
}

func assertMounted(t *testing.T, mountPoint string) {
	t.Helper()
	out := mountOutput(t)
	re := regexp.MustCompile(`\son\s` + regexp.QuoteMeta(mountPoint) + `\s`)
	if !re.MatchString(out) {
		t.Fatalf("expected %s to be mounted; mount output:\n%s", mountPoint, out)
	}
}

func assertNotMounted(t *testing.T, mountPoint string) {
	t.Helper()
	out := mountOutput(t)
	re := regexp.MustCompile(`\son\s` + regexp.QuoteMeta(mountPoint) + `\s`)
	if re.MatchString(out) {
		t.Fatalf("expected %s to be unmounted; mount output:\n%s", mountPoint, out)
	}
}

// TestOverlayMountLifecycle ensures Start returns only after overlay mounts
// and Shutdown returns only after overlay unmounts. It validates using the
// system's mount table, not internal state.
func TestOverlayMountLifecycle(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	// Prepare environment
	testDir := SetupTestEnvironment(t)

	// Create a valid lower path for overlayfs to use
	lower := filepath.Join(testDir, "lower")
	if err := os.MkdirAll(lower, 0755); err != nil {
		t.Fatalf("failed to create lower dir: %v", err)
	}

	// Configure overlay + JuiceFS local mode (must set JuiceFSDataPath explicitly in tests)
	config := TestConfig(testDir)
	config.JuiceFSLocalMode = true
	// Use a separate temp base for JuiceFS to avoid interfering with t.TempDir cleanup
	juiceBase, err := os.MkdirTemp("", "sprite-juicefs-*")
	if err != nil {
		t.Fatalf("failed to create juicefs base: %v", err)
	}
	t.Cleanup(func() {
		// Best-effort cleanup; ignore errors
		_ = os.RemoveAll(juiceBase)
	})
	config.JuiceFSDataPath = juiceBase
	config.OverlayEnabled = true
	config.OverlayLowerPaths = []string{lower}
	// Use default mount points: /mnt/user-data and /mnt/newroot
	if config.OverlayTargetPath == "" {
		config.OverlayTargetPath = "/mnt/newroot"
	}

	sys, cleanup, err := TestSystem(config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start and block until storage ready (Start should already block on mount)
	StartSystemWithTimeout(t, sys, 30*time.Second)

	// Additionally wait on WhenStorageReady to ensure readiness path remains correct
	ctx, cancel := context.WithTimeout(context.Background(), 15*time.Second)
	defer cancel()
	if err := sys.WhenStorageReady(ctx); err != nil {
		t.Fatalf("WhenStorageReady error: %v", err)
	}

	// Validate mounts are present
	assertMounted(t, "/mnt/user-data")
	if !config.OverlaySkipOverlayFS {
		assertMounted(t, config.OverlayTargetPath)
	}

	// Shutdown and ensure unmounted when it returns
	ctx2, cancel2 := context.WithTimeout(context.Background(), 60*time.Second)
	defer cancel2()
	if err := sys.Shutdown(ctx2); err != nil {
		t.Fatalf("Shutdown error: %v", err)
	}

	// Validate unmounted
	assertNotMounted(t, "/mnt/user-data")
	if !config.OverlaySkipOverlayFS {
		assertNotMounted(t, config.OverlayTargetPath)
	}
}

// TestPartialShutdownAndBoot validates we can stop container components and start them again
func TestPartialShutdownAndBoot(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)
	lower := filepath.Join(testDir, "lower2")
	if err := os.MkdirAll(lower, 0755); err != nil {
		t.Fatalf("failed to create lower dir: %v", err)
	}

	config := VerboseTestConfig(testDir)
	config.JuiceFSLocalMode = true
	juiceBase, err := os.MkdirTemp("", "sprite-juicefs-*")
	if err != nil {
		t.Fatalf("failed to create juicefs base: %v", err)
	}
	t.Cleanup(func() { _ = os.RemoveAll(juiceBase) })
	config.JuiceFSDataPath = juiceBase
	config.OverlayEnabled = true
	config.OverlayLowerPaths = []string{lower}
	if config.OverlayTargetPath == "" {
		config.OverlayTargetPath = "/mnt/newroot"
	}

	sys, cleanup, err := TestSystem(config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Boot container components only (15s)
	ctx, cancel := context.WithTimeout(context.Background(), 15*time.Second)
	defer cancel()
	logTS(t, "BootContainer: starting")
	if err := sys.BootContainer(ctx); err != nil {
		t.Fatalf("BootContainer error: %v", err)
	}
	logTS(t, "BootContainer: done")

	// Validate mounts present
	assertMounted(t, "/mnt/user-data")
	if !config.OverlaySkipOverlayFS {
		assertMounted(t, config.OverlayTargetPath)
	}

	// Now stop container components (15s)
	ctxStop, cancelStop := context.WithTimeout(context.Background(), 15*time.Second)
	defer cancelStop()
	logTS(t, "ShutdownContainer: starting")
	if err := sys.ShutdownContainer(ctxStop); err != nil {
		t.Fatalf("ShutdownContainer error: %v", err)
	}
	logTS(t, "ShutdownContainer: done")

	// Inspect system state before second boot
	dumpCmd(t, "mount")
	dumpCmd(t, "losetup", "-a")

	// Validate unmounted
	assertNotMounted(t, "/mnt/user-data")
	if !config.OverlaySkipOverlayFS {
		assertNotMounted(t, config.OverlayTargetPath)
	}

	// Start again (15s)
	ctx2, cancel2 := context.WithTimeout(context.Background(), 15*time.Second)
	defer cancel2()
	logTS(t, "BootContainer(second): starting")
	dumpCmd(t, "mount")
	dumpCmd(t, "losetup", "-a")
	if err := sys.BootContainer(ctx2); err != nil {
		t.Fatalf("BootContainer (second) error: %v", err)
	}
	logTS(t, "BootContainer(second): done")

	// Validate mounted again
	assertMounted(t, "/mnt/user-data")
	if !config.OverlaySkipOverlayFS {
		assertMounted(t, config.OverlayTargetPath)
	}

	// Clean stop (15s)
	ctx3, cancel3 := context.WithTimeout(context.Background(), 15*time.Second)
	defer cancel3()
	logTS(t, "ShutdownContainer(final): starting")
	if err := sys.ShutdownContainer(ctx3); err != nil {
		t.Fatalf("final ShutdownContainer error: %v", err)
	}
	logTS(t, "ShutdownContainer(final): done")
}
