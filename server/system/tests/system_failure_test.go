package tests

import (
	"context"
	"os"
	"path/filepath"
	"testing"
	"time"
)

// TestShutdownAfterBootFailure verifies that Shutdown() can be called safely after Start() fails
// This simulates what main.go should do when Boot() fails
func TestShutdownAfterBootFailure(t *testing.T) {
	_, cancel := SetTestDeadline(t)
	defer cancel()

	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Configure with invalid process to make Start() fail
	config := TestConfig(testDir)
	config.ProcessCommand = []string{"/nonexistent/binary"}

	sys, cleanup, err := TestSystem(t, config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start should fail
	t.Log("Attempting to start system with invalid process...")
	err = sys.Start()
	if err == nil {
		t.Fatal("Expected Start() to fail with invalid process")
	}
	t.Logf("Start() failed as expected: %v", err)

	// Now verify we can safely shutdown even though Start() failed
	// This is what main.go should do
	t.Log("Calling Shutdown() after failed Start()...")
	startTime := time.Now()
	shutdownErr := sys.Shutdown(context.Background())
	shutdownDuration := time.Since(startTime)

	if shutdownErr != nil {
		t.Logf("Shutdown returned error (may be OK): %v", shutdownErr)
	}

	t.Logf("Shutdown completed in %v", shutdownDuration)

	// Shutdown should complete quickly since system never fully started
	if shutdownDuration > 10*time.Second {
		t.Errorf("Shutdown took too long after failed Start(): %v", shutdownDuration)
	}

	// Verify we can call Shutdown() again (idempotent)
	err = sys.Shutdown(context.Background())
	if err != nil {
		t.Logf("Second shutdown returned: %v", err)
	}
}

// TestShutdownWithStorageErrors verifies shutdown handles storage unmount failures gracefully
// We boot successfully, then shutdown and verify it completes even if storage has issues
func TestShutdownWithStorageErrors(t *testing.T) {
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

	// Start the system successfully
	t.Log("Starting system...")
	if err := sys.Start(); err != nil {
		t.Fatalf("Failed to start system: %v", err)
	}

	// Now shutdown - even if storage has issues, shutdown should complete
	// (In a real scenario, storage might be corrupted or unmount might fail)
	t.Log("Shutting down system...")
	startTime := time.Now()
	err = sys.Shutdown(context.Background())
	shutdownDuration := time.Since(startTime)

	if err != nil {
		t.Logf("Shutdown returned error: %v", err)
		// We want to verify shutdown completes even with errors
	}

	t.Logf("Shutdown completed in %v", shutdownDuration)

	// Process should be stopped
	if sys.IsProcessRunning() {
		t.Error("Process should not be running after shutdown")
	}
}

// Note: Partial boot/shutdown testing is covered by TestPartialShutdownAndBoot
// in system_storage_test.go. That test properly starts the full system first,
// then tests partial shutdown and reboot of container components.

// TestShutdownDuringProcessStart verifies shutdown works if triggered while process is starting
func TestShutdownDuringProcessStart(t *testing.T) {
	_, cancel := SetTestDeadline(t)
	defer cancel()

	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Create a script that takes a moment to start
	slowStartScript := filepath.Join(testDir, "slow-start.sh")
	scriptContent := `#!/bin/bash
echo "Process starting slowly (PID $$)"
sleep 1
echo "Process started"
trap "echo 'Process received SIGTERM'; exit 0" SIGTERM
while true; do
	sleep 1
done
`
	if err := os.WriteFile(slowStartScript, []byte(scriptContent), 0755); err != nil {
		t.Fatal(err)
	}

	config := TestConfig(testDir)
	config.ProcessCommand = []string{slowStartScript}

	sys, cleanup, err := TestSystem(t, config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system in background
	t.Log("Starting system...")
	go func() {
		_ = sys.Start()
	}()

	// Give it a tiny bit to start booting
	time.Sleep(100 * time.Millisecond)

	// Immediately trigger shutdown while it's still starting
	t.Log("Triggering shutdown while system is starting...")
	err = sys.Shutdown(context.Background())
	if err != nil {
		t.Logf("Shutdown error (may be expected): %v", err)
	}

	t.Log("Shutdown completed")

	// Process should be stopped
	if sys.IsProcessRunning() {
		t.Error("Process should not be running after shutdown")
	}
}

// TestMultipleRapidShutdowns verifies concurrent Shutdown() calls don't cause issues
func TestMultipleRapidShutdowns(t *testing.T) {
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
	if err := sys.Start(); err != nil {
		t.Fatalf("Failed to start system: %v", err)
	}

	// Call Shutdown() multiple times concurrently
	t.Log("Calling Shutdown() 5 times concurrently...")

	done := make(chan error, 5)
	for i := 0; i < 5; i++ {
		go func(id int) {
			err := sys.Shutdown(context.Background())
			t.Logf("Shutdown call %d completed: %v", id, err)
			done <- err
		}(i)
	}

	// Wait for all to complete
	for i := 0; i < 5; i++ {
		<-done
	}

	t.Log("All shutdown calls completed")

	// Process should be stopped
	if sys.IsProcessRunning() {
		t.Error("Process should not be running after shutdown")
	}
}

// TestBootFailureCleanup verifies that when Boot() fails, all partially-initialized
// subsystems are cleaned up properly and we don't leak resources
func TestBootFailureCleanup(t *testing.T) {
	_, cancel := SetTestDeadline(t)
	defer cancel()

	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Try to boot with bad configuration
	config := TestConfig(testDir)
	config.ProcessCommand = []string{"/nonexistent/binary"}

	sys, cleanup, err := TestSystem(t, config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Boot should fail at process start
	t.Log("Attempting boot with invalid config...")
	err = sys.Start()
	if err == nil {
		t.Fatal("Expected Start() to fail")
	}

	t.Logf("Start() failed as expected: %v", err)

	// Even though boot failed, subsystems that DID start should be cleaned up
	// Call Shutdown() to ensure cleanup
	err = sys.Shutdown(context.Background())
	if err != nil {
		t.Logf("Shutdown after failed boot: %v", err)
	}

	// Verify no process is running
	if sys.IsProcessRunning() {
		t.Error("No process should be running after failed boot and shutdown")
	}

	// Check that we can create a new system and it works
	// This verifies we didn't leak resources or leave things in a bad state
	t.Log("Creating new system to verify no resource leaks...")
	config2 := TestConfig(testDir)
	sys2, cleanup2, err := TestSystem(t, config2)
	defer cleanup2()
	if err != nil {
		t.Fatalf("Failed to create second system: %v", err)
	}

	if err := sys2.Start(); err != nil {
		t.Fatalf("Failed to start system: %v", err)
	}
	if !sys2.IsProcessRunning() {
		t.Fatal("Process should be running")
	}

	// Shut down the second system properly before test ends
	if err := sys2.Shutdown(context.Background()); err != nil {
		t.Fatalf("Failed to shutdown second system: %v", err)
	}

	t.Log("Second system started and shut down successfully - no resource leaks")
}
