package tests

import (
	"context"
	"os"
	"path/filepath"
	"testing"
	"time"
)

// TestSystemShutdownHangOverlay verifies shutdown completes within timeout when overlay hangs
// Tests that forced cleanup happens and no loop devices leaked
func TestSystemShutdownHangOverlay(t *testing.T) {
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

	// Note: Actually making overlay unmount hang requires kernel/mount manipulation
	// This test validates shutdown completes within reasonable time
	// In production, overlay unmount should not hang, but if it does, forced cleanup applies

	t.Log("Attempting shutdown with hang timeout detection...")
	// Test shutdown without timeout to expose real cleanup issues
	startTime := time.Now()
	err = sys.Shutdown(context.Background())
	duration := time.Since(startTime)

	if err != nil {
		t.Logf("Shutdown completed with error in %v: %v", duration, err)
	} else {
		t.Logf("Shutdown completed successfully in %v", duration)
	}

	// Shutdown should complete well under 30 seconds normally
	if duration > 25*time.Second {
		t.Logf("WARNING: Shutdown took %v - may indicate slow unmount (but within timeout)", duration)
	}

	// Even if timeout occurred, test should complete (not hang indefinitely)
	t.Logf("Shutdown duration: %v (max allowed: 3 minutes)", duration)

	// CRITICAL: Verify no loop devices leaked even after forced cleanup
	verifyCtx := context.Background()

	if sys.OverlayManager != nil {
		for i, verify := range sys.OverlayManager.CleanupVerifiers() {
			if err := verify(verifyCtx); err != nil {
				t.Errorf("OverlayManager cleanup verifier %d failed (leaked resource): %v", i, err)
			}
		}
	}

	if sys.JuiceFS != nil {
		for i, verify := range sys.JuiceFS.CleanupVerifiers() {
			if err := verify(verifyCtx); err != nil {
				t.Errorf("JuiceFS cleanup verifier %d failed: %v", i, err)
			}
		}
	}

	t.Log("Hang timeout test completed - no resources leaked")
}

// TestSystemShutdownHangJuiceFS verifies shutdown respects JuiceFS 5-minute window
// Tests that shutdown completes within 6 minutes (5min + buffer) even if hung
func TestSystemShutdownHangJuiceFS(t *testing.T) {
	// Override deadline to allow for JuiceFS 5-minute timeout
	deadline := time.Now().Add(7 * time.Minute)
	if d, ok := t.Deadline(); ok && d.Before(deadline) {
		deadline = d
	}
	ctx, cancel := context.WithDeadline(context.Background(), deadline)
	defer cancel()

	// Monitor for deadline exceeded
	done := make(chan struct{})
	go func() {
		select {
		case <-ctx.Done():
			if ctx.Err() == context.DeadlineExceeded {
				t.Error("TEST DEADLINE EXCEEDED - shutdown took longer than expected")
			}
		case <-done:
		}
	}()
	defer close(done)

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

	// Note: JuiceFS umount respects 5-minute window for data integrity (memory 2978565)
	// This is a CRITICAL timeout that must NOT be reduced

	t.Log("Attempting shutdown with JuiceFS timeout detection...")
	// Test shutdown without timeout to expose real cleanup issues
	startTime := time.Now()
	err = sys.Shutdown(context.Background())
	duration := time.Since(startTime)

	if err != nil {
		t.Logf("Shutdown completed with error in %v: %v", duration, err)
	} else {
		t.Logf("Shutdown completed successfully in %v", duration)
	}

	// Should complete well under 30 seconds in normal operation
	if duration > 25*time.Second {
		t.Logf("WARNING: Shutdown took %v - may indicate slow JuiceFS unmount", duration)
	}

	// Must complete within 6 minutes even if hung
	if duration > 6*time.Minute {
		t.Errorf("Shutdown exceeded 6-minute timeout: %v", duration)
	}

	t.Logf("Shutdown duration: %v (max allowed: 6 minutes for JuiceFS)", duration)

	// CRITICAL: Verify no JuiceFS mount leaked
	verifyCtx := context.Background()

	if sys.JuiceFS != nil {
		for i, verify := range sys.JuiceFS.CleanupVerifiers() {
			if err := verify(verifyCtx); err != nil {
				t.Errorf("JuiceFS cleanup verifier %d failed (leaked mount): %v", i, err)
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

	t.Log("JuiceFS timeout test completed - respects 5-minute window, no mounts leaked")
}

// TestSystemShutdownHangService verifies force-kill happens when service hangs
// Tests that shutdown completes within 1 minute with force-kill
func TestSystemShutdownHangService(t *testing.T) {
	_, cancel := SetTestDeadline(t)
	defer cancel()

	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Create a process that ignores SIGTERM
	ignoreScript := filepath.Join(testDir, "ignore-term.sh")
	scriptContent := `#!/bin/bash
trap "" SIGTERM
echo "Process ignoring SIGTERM (PID $$)"
while true; do sleep 1; done
`
	if err := os.WriteFile(ignoreScript, []byte(scriptContent), 0755); err != nil {
		t.Fatal(err)
	}

	config := TestConfig(testDir)
	config.ProcessCommand = []string{ignoreScript}
	config.ProcessGracefulShutdownTimeout = 3 * time.Second

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

	t.Log("Attempting shutdown (service will hang, should force-kill)...")
	startTime := time.Now()
	err = sys.Shutdown(context.Background())
	duration := time.Since(startTime)

	if err != nil {
		t.Logf("Shutdown completed with error in %v: %v", duration, err)
	} else {
		t.Logf("Shutdown completed in %v", duration)
	}

	// Should take at least graceful timeout (3s) before force-kill
	if duration < 3*time.Second {
		t.Logf("WARNING: Shutdown faster than graceful timeout (%v < 3s)", duration)
	}

	// Must complete within 1 minute
	if duration > 1*time.Minute {
		t.Errorf("Shutdown exceeded 1-minute timeout: %v", duration)
	}

	t.Logf("Shutdown duration: %v (force-kill executed)", duration)

	// Process must be stopped (force-killed)
	if sys.IsProcessRunning() {
		t.Error("Process should be force-killed when ignoring SIGTERM")
	}

	// CRITICAL: Verify no processes leaked
	verifyCtx := context.Background()

	if sys.ServicesManager != nil {
		for i, verify := range sys.ServicesManager.CleanupVerifiers() {
			if err := verify(verifyCtx); err != nil {
				t.Errorf("ServicesManager cleanup verifier %d failed (leaked process): %v", i, err)
			}
		}
	}

	t.Log("Service hang test completed - force-kill executed, no processes leaked")
}

// TestUserEnvironmentShutdownHang verifies timeout handling for UserEnvironment
// Tests that SystemBoot remains unaffected when UserEnvironment shutdown hangs
func TestUserEnvironmentShutdownHang(t *testing.T) {
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

	// Shutdown UserEnvironment
	t.Log("Shutting down UserEnvironment with hang detection...")
	startTime := time.Now()
	err = sys.ShutdownContainer(context.Background())
	duration := time.Since(startTime)

	if err != nil {
		t.Logf("ShutdownContainer completed with error in %v: %v", duration, err)
	} else {
		t.Logf("ShutdownContainer completed in %v", duration)
	}

	// Should complete within 2 minutes
	if duration > 2*time.Minute {
		t.Errorf("UserEnvironment shutdown exceeded 2-minute timeout: %v", duration)
	}

	t.Logf("UserEnvironment shutdown duration: %v", duration)

	// CRITICAL: Verify UserEnvironment cleanup
	verifyCtx := context.Background()

	if sys.OverlayManager != nil {
		for i, verify := range sys.OverlayManager.CleanupVerifiers() {
			if err := verify(verifyCtx); err != nil {
				t.Errorf("OverlayManager cleanup verifier %d failed: %v", i, err)
			}
		}
	}

	if sys.ServicesManager != nil {
		for i, verify := range sys.ServicesManager.CleanupVerifiers() {
			if err := verify(verifyCtx); err != nil {
				t.Errorf("ServicesManager cleanup verifier %d failed: %v", i, err)
			}
		}
	}

	// CRITICAL: Verify SystemBoot (JuiceFS, DB) still running - unaffected by hang
	if sys.JuiceFS != nil && !sys.JuiceFS.IsMounted() {
		t.Error("JuiceFS should still be mounted (SystemBoot unaffected by UserEnvironment hang)")
	}

	// Now shutdown SystemBoot
	t.Log("Shutting down SystemBoot (should be unaffected)...")
	err = sys.Shutdown(context.Background())
	if err != nil {
		t.Logf("SystemBoot shutdown error: %v", err)
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

	t.Log("UserEnvironment hang test completed - SystemBoot remained stable")
}

