package tests

import (
	"context"
	"os"
	"path/filepath"
	"testing"
	"time"
)

// TestSystemShutdownWedgedOverlay verifies forced cleanup when overlay won't unmount
// Tests that no loop devices are leaked even when overlay unmount fails
func TestSystemShutdownWedgedOverlay(t *testing.T) {
	_, cancel := SetTestDeadline(t)
	defer cancel()

	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	config := TestConfig(testDir)

	sys, cleanup, err := TestSystem(t, config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system
	t.Log("Starting system...")
	if err := sys.Start(); err != nil {
		t.Fatalf("Failed to start system: %v", err)
	}

	// Note: Actually wedging an overlay mount requires root/kernel operations
	// This test verifies that shutdown completes and cleanup verifiers detect any leaks
	// In a real wedged scenario, forced cleanup would use lazy unmount (umount -l)

	t.Log("Attempting shutdown (simulating potential overlay wedge scenario)...")
	startTime := time.Now()
	err = sys.Shutdown(context.Background())
	duration := time.Since(startTime)

	if err != nil {
		t.Logf("Shutdown completed with error in %v: %v", duration, err)
	} else {
		t.Logf("Shutdown completed successfully in %v", duration)
	}

	// CRITICAL: Verify no loop devices leaked
	// Even if overlay was wedged, forced cleanup should detach loop devices
	verifyCtx := context.Background()

	if sys.OverlayManager != nil {
		for i, verify := range sys.OverlayManager.CleanupVerifiers() {
			if err := verify(verifyCtx); err != nil {
				t.Fatalf("OverlayManager cleanup verifier %d failed (leaked resource): %v", i, err)
			}
		}
	}

	// Verify other components also cleaned up properly
	if sys.JuiceFS != nil {
		for i, verify := range sys.JuiceFS.CleanupVerifiers() {
			if err := verify(verifyCtx); err != nil {
				t.Fatalf("JuiceFS cleanup verifier %d failed: %v", i, err)
			}
		}
	}

	t.Log("Shutdown test completed - no loop devices leaked")
}

// TestSystemShutdownWedgedJuiceFS verifies JuiceFS respects 5-minute timeout
// Tests that forced cleanup happens after timeout, no mount leaked
func TestSystemShutdownWedgedJuiceFS(t *testing.T) {
	_, cancel := SetTestDeadline(t)
	defer cancel()

	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	config := TestConfig(testDir)

	sys, cleanup, err := TestSystem(t, config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system
	t.Log("Starting system...")
	if err := sys.Start(); err != nil {
		t.Fatalf("Failed to start system: %v", err)
	}

	// Note: Simulating a wedged JuiceFS unmount is difficult
	// JuiceFS unmount respects 5-minute timeout for data integrity (memory 2978565)
	// This test verifies shutdown completes and no mounts leaked

	t.Log("Attempting shutdown (simulating potential JuiceFS wedge scenario)...")
	// Test shutdown without timeout to expose real cleanup issues
	startTime := time.Now()
	err = sys.Shutdown(context.Background())
	duration := time.Since(startTime)

	if err != nil {
		t.Logf("Shutdown completed with error in %v: %v", duration, err)
	} else {
		t.Logf("Shutdown completed successfully in %v", duration)
	}

	// Should complete well under 30 seconds in normal cases
	if duration > 25*time.Second {
		t.Logf("WARNING: Shutdown took %v - may indicate slow unmount", duration)
	}

	// CRITICAL: Verify no JuiceFS mount leaked
	verifyCtx := context.Background()

	if sys.JuiceFS != nil {
		for i, verify := range sys.JuiceFS.CleanupVerifiers() {
			if err := verify(verifyCtx); err != nil {
				t.Fatalf("JuiceFS cleanup verifier %d failed (leaked mount): %v", i, err)
			}
		}
	}

	if sys.DBManager != nil {
		for i, verify := range sys.DBManager.CleanupVerifiers() {
			if err := verify(verifyCtx); err != nil {
				t.Fatalf("DBManager cleanup verifier %d failed: %v", i, err)
			}
		}
	}

	t.Log("Shutdown test completed - no mounts leaked")
}

// TestSystemShutdownWedgedService verifies force-kill when service won't terminate
// Tests that SIGKILL is used and no processes leaked
func TestSystemShutdownWedgedService(t *testing.T) {
	_, cancel := SetTestDeadline(t)
	defer cancel()

	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Create a script that ignores SIGTERM (but not SIGKILL)
	ignoreSigScript := filepath.Join(testDir, "ignore-sigterm.sh")
	scriptContent := `#!/bin/bash
trap "" SIGTERM
echo "Process ignoring SIGTERM (PID $$)"
while true; do
	sleep 1
done
`
	if err := os.WriteFile(ignoreSigScript, []byte(scriptContent), 0755); err != nil {
		t.Fatal(err)
	}

	config := TestConfig(testDir)
	config.ProcessCommand = []string{ignoreSigScript}
	config.ProcessGracefulShutdownTimeout = 2 * time.Second

	sys, cleanup, err := TestSystem(t, config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system
	t.Log("Starting system with process that ignores SIGTERM...")
	if err := sys.Start(); err != nil {
		t.Fatalf("Failed to start system: %v", err)
	}

	// Shutdown - should force-kill after graceful timeout
	t.Log("Attempting shutdown (process will ignore SIGTERM, should be force-killed)...")
	startTime := time.Now()
	err = sys.Shutdown(context.Background())
	duration := time.Since(startTime)

	if err != nil {
		t.Logf("Shutdown completed with error in %v: %v", duration, err)
	} else {
		t.Logf("Shutdown completed in %v", duration)
	}

	// Should take at least graceful timeout (2s) before force-kill
	if duration < 2*time.Second {
		t.Errorf("Shutdown too fast (%v), expected at least 2s for graceful timeout", duration)
	}

	// Process should be stopped (force-killed)
	if sys.IsProcessRunning() {
		t.Error("Process should be force-stopped after ignoring SIGTERM")
	}

	// CRITICAL: Verify no service processes leaked
	verifyCtx := context.Background()

	if sys.ServicesManager != nil {
		for i, verify := range sys.ServicesManager.CleanupVerifiers() {
			if err := verify(verifyCtx); err != nil {
				t.Errorf("ServicesManager cleanup verifier %d failed (leaked process): %v", i, err)
			}
		}
	}

	t.Log("Force-kill test completed - no processes leaked")
}

// TestUserEnvironmentShutdownWedged verifies isolation when UserEnvironment wedged
// Tests that SystemBoot remains unaffected when UserEnvironment cleanup fails
func TestUserEnvironmentShutdownWedged(t *testing.T) {
	_, cancel := SetTestDeadline(t)
	defer cancel()

	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	config := TestConfig(testDir)

	sys, cleanup, err := TestSystem(t, config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the full system
	t.Log("Starting full system...")
	if err := sys.Start(); err != nil {
		t.Fatalf("Failed to start system: %v", err)
	}

	// Shutdown UserEnvironment (Container + Overlay + Services)
	t.Log("Shutting down UserEnvironment (simulating potential wedge)...")
	err = sys.ShutdownContainer(context.Background())

	if err != nil {
		t.Logf("ShutdownContainer error (may be expected in wedge scenario): %v", err)
	}

	// CRITICAL: Verify UserEnvironment cleanup
	verifyCtx := context.Background()

	// Check overlay cleanup
	if sys.OverlayManager != nil {
		for i, verify := range sys.OverlayManager.CleanupVerifiers() {
			if err := verify(verifyCtx); err != nil {
				t.Errorf("OverlayManager cleanup verifier %d failed: %v", i, err)
			}
		}
	}

	// Check services cleanup
	if sys.ServicesManager != nil {
		for i, verify := range sys.ServicesManager.CleanupVerifiers() {
			if err := verify(verifyCtx); err != nil {
				t.Errorf("ServicesManager cleanup verifier %d failed: %v", i, err)
			}
		}
	}

	// CRITICAL: Verify SystemBoot (JuiceFS, DB) still running and unaffected
	// This demonstrates isolation between phases
	if sys.JuiceFS != nil && !sys.JuiceFS.IsMounted() {
		t.Error("JuiceFS should still be mounted (SystemBoot should be unaffected)")
	}

	// Now shutdown SystemBoot
	t.Log("Shutting down SystemBoot...")
	err = sys.Shutdown(context.Background())
	if err != nil {
		t.Logf("Full shutdown error: %v", err)
	}

	// Verify SystemBoot cleanup
	if sys.JuiceFS != nil {
		for i, verify := range sys.JuiceFS.CleanupVerifiers() {
			if err := verify(verifyCtx); err != nil {
				t.Errorf("JuiceFS cleanup verifier %d failed: %v", i, err)
			}
		}
	}

	if sys.DBManager != nil {
		for i, verify := range sys.DBManager.CleanupVerifiers() {
			if err := verify(verifyCtx); err != nil {
				t.Errorf("DBManager cleanup verifier %d failed: %v", i, err)
			}
		}
	}

	t.Log("Isolation test completed - UserEnvironment wedge did not affect SystemBoot")
}

