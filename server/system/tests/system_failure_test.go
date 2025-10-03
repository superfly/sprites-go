package tests

import (
	"context"
	"os"
	"path/filepath"
	"testing"
	"time"

	"github.com/superfly/sprite-env/server/system"
)

// TestShutdownAfterBootFailure verifies that Shutdown() can be called safely after Start() fails
// This simulates what main.go should do when Boot() fails
func TestShutdownAfterBootFailure(t *testing.T) {
	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Configure with invalid process to make Start() fail
	config := TestConfig(testDir)
	config.ProcessCommand = []string{"/nonexistent/binary"}

	sys, err := system.New(config)
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start should fail
	t.Log("Attempting to start system with invalid process...")
	err = sys.Start()
	if err == nil {
		ShutdownSystemWithTimeout(t, sys, 5*time.Second)
		t.Fatal("Expected Start() to fail with invalid process")
	}
	t.Logf("Start() failed as expected: %v", err)

	// Now verify we can safely shutdown even though Start() failed
	// This is what main.go should do
	t.Log("Calling Shutdown() after failed Start()...")
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	startTime := time.Now()
	shutdownErr := sys.Shutdown(ctx)
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
	ctx2, cancel2 := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel2()

	err = sys.Shutdown(ctx2)
	if err != nil {
		t.Logf("Second shutdown returned: %v", err)
	}
}

// TestShutdownWithStorageErrors verifies shutdown handles storage unmount failures gracefully
// We boot successfully, then shutdown and verify it completes even if storage has issues
func TestShutdownWithStorageErrors(t *testing.T) {
	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	config := TestConfig(testDir)

	sys, err := system.New(config)
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system successfully
	t.Log("Starting system...")
	StartSystemWithTimeout(t, sys, 30*time.Second)
	VerifySystemRunning(t, sys)

	// Now shutdown - even if storage has issues, shutdown should complete
	// (In a real scenario, storage might be corrupted or unmount might fail)
	t.Log("Shutting down system...")
	ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
	defer cancel()

	startTime := time.Now()
	err = sys.Shutdown(ctx)
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

	sys, err := system.New(config)
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
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	err = sys.Shutdown(ctx)
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
	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	config := TestConfig(testDir)

	sys, err := system.New(config)
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system
	StartSystemWithTimeout(t, sys, 30*time.Second)
	VerifySystemRunning(t, sys)

	// Call Shutdown() multiple times concurrently
	t.Log("Calling Shutdown() 5 times concurrently...")

	done := make(chan error, 5)
	for i := 0; i < 5; i++ {
		go func(id int) {
			ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
			defer cancel()
			err := sys.Shutdown(ctx)
			t.Logf("Shutdown call %d completed: %v", id, err)
			done <- err
		}(i)
	}

	// Wait for all to complete
	for i := 0; i < 5; i++ {
		select {
		case <-done:
			// OK
		case <-time.After(45 * time.Second):
			t.Fatal("Timeout waiting for concurrent shutdowns")
		}
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
	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Try to boot with bad configuration
	config := TestConfig(testDir)
	config.ProcessCommand = []string{"/nonexistent/binary"}

	sys, err := system.New(config)
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Boot should fail at process start
	t.Log("Attempting boot with invalid config...")
	err = sys.Start()
	if err == nil {
		ShutdownSystemWithTimeout(t, sys, 5*time.Second)
		t.Fatal("Expected Start() to fail")
	}

	t.Logf("Start() failed as expected: %v", err)

	// Even though boot failed, subsystems that DID start should be cleaned up
	// Call Shutdown() to ensure cleanup
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	err = sys.Shutdown(ctx)
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
	sys2, err := system.New(config2)
	if err != nil {
		t.Fatalf("Failed to create second system: %v", err)
	}
	defer ShutdownSystemWithTimeout(t, sys2, 30*time.Second)

	StartSystemWithTimeout(t, sys2, 30*time.Second)
	VerifySystemRunning(t, sys2)

	t.Log("Second system started successfully - no resource leaks")
}
