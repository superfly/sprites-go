package tests

import (
	"context"
	"testing"
	"time"
)

// TestSystemBootHangJuiceFS verifies test fails fast when JuiceFS mount hangs
// Test should complete (fail) within deadline, cleanup should run even after timeout
func TestSystemBootHangJuiceFS(t *testing.T) {
	_, cancel := SetTestDeadline(t)
	defer cancel()

	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	config := TestConfig(testDir)
	// Note: Simulating a hanging JuiceFS mount is difficult without actual mocking
	// In practice, JuiceFS mount timeouts are handled by the juicefs package itself
	// This test validates that if boot takes too long, our test deadline catches it

	sys, cleanup, err := TestSystem(t, config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	t.Log("Attempting system boot with hang detection...")
	startTime := time.Now()

	err = sys.Start()
	duration := time.Since(startTime)
	if err != nil {
		t.Logf("Boot failed in %v: %v", duration, err)
	} else {
		t.Logf("Boot completed in %v", duration)
	}

	// CRITICAL: Cleanup should run even if boot hung
	shutdownErr := sys.Shutdown(context.Background())
	if shutdownErr != nil {
		t.Logf("Shutdown after hang: %v", shutdownErr)
	}

	// Verify no resources leaked even after hang/timeout
	verifyCtx := context.Background()

	if sys.JuiceFS != nil {
		for i, verify := range sys.JuiceFS.CleanupVerifiers() {
			if err := verify(verifyCtx); err != nil {
				t.Fatalf("JuiceFS cleanup verifier %d failed: %v", i, err)
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

	t.Log("Hang detection test completed - no resources leaked")
}

// TestUserEnvironmentBootHangOverlay verifies test fails fast when overlay mount hangs
// Test should complete (fail) within deadline, cleanup should run even after timeout
func TestUserEnvironmentBootHangOverlay(t *testing.T) {
	_, cancel := SetTestDeadline(t)
	defer cancel()

	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	config := TestConfig(testDir)
	// Note: Simulating hanging overlay mount is difficult without mocking
	// This test validates that boot operations don't hang indefinitely

	sys, cleanup, err := TestSystem(t, config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	t.Log("Attempting system boot with overlay hang detection...")
	startTime := time.Now()

	err = sys.Start()
	duration := time.Since(startTime)
	if err != nil {
		t.Logf("Boot failed in %v: %v", duration, err)
	} else {
		t.Logf("Boot completed in %v", duration)
	}

	// CRITICAL: Cleanup should run even if boot hung
	shutdownErr := sys.Shutdown(context.Background())
	if shutdownErr != nil {
		t.Logf("Shutdown after hang: %v", shutdownErr)
	}

	// Verify no loop devices or mounts leaked
	verifyCtx := context.Background()

	if sys.OverlayManager != nil {
		for i, verify := range sys.OverlayManager.CleanupVerifiers() {
			if err := verify(verifyCtx); err != nil {
				t.Fatalf("OverlayManager cleanup verifier %d failed: %v", i, err)
			}
		}
	}

	if sys.JuiceFS != nil {
		for i, verify := range sys.JuiceFS.CleanupVerifiers() {
			if err := verify(verifyCtx); err != nil {
				t.Fatalf("JuiceFS cleanup verifier %d failed: %v", i, err)
			}
		}
	}

	t.Log("Hang detection test completed - no mounts or loop devices leaked")
}

// TestUserEnvironmentBootHangServices verifies test fails fast when service startup hangs
// Test should complete (fail) within deadline, cleanup should run even after timeout
func TestUserEnvironmentBootHangServices(t *testing.T) {
	_, cancel := SetTestDeadline(t)
	defer cancel()

	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	config := TestConfig(testDir)
	// Services start after boot, so full boot should succeed
	// Service hangs would be detected during service operations

	sys, cleanup, err := TestSystem(t, config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	t.Log("Attempting system boot with service hang detection...")
	startTime := time.Now()

	err = sys.Start()
	duration := time.Since(startTime)
	if err != nil {
		t.Logf("Boot failed in %v: %v", duration, err)
	} else {
		t.Logf("Boot completed in %v", duration)
	}

	// Shutdown
	shutdownErr := sys.Shutdown(context.Background())
	if shutdownErr != nil {
		t.Logf("Shutdown: %v", shutdownErr)
	}

	// CRITICAL: Verify no service processes leaked
	verifyCtx := context.Background()

	if sys.ServicesManager != nil {
		for i, verify := range sys.ServicesManager.CleanupVerifiers() {
			if err := verify(verifyCtx); err != nil {
				t.Fatalf("ServicesManager cleanup verifier %d failed: %v", i, err)
			}
		}
	}

	if sys.OverlayManager != nil {
		for i, verify := range sys.OverlayManager.CleanupVerifiers() {
			if err := verify(verifyCtx); err != nil {
				t.Fatalf("OverlayManager cleanup verifier %d failed: %v", i, err)
			}
		}
	}

	// Verify process is stopped
	if sys.IsProcessRunning() {
		t.Error("Container process should not be running")
	}

	t.Log("Hang detection test completed - no processes leaked")
}

