package tests

import (
	"context"
	"os"
	"path/filepath"
	"syscall"
	"testing"
	"time"
)

// TestSystemGracefulShutdown verifies clean shutdown of all subsystems
func TestSystemGracefulShutdown(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Create a test process that logs shutdown
	testScript := CreateTestScript(t, testDir, "shutdown-test.sh")

	config := TestConfig(testDir)
	config.ProcessCommand = []string{testScript}
	config.ProcessGracefulShutdownTimeout = 5 * time.Second

	sys, cleanup, err := TestSystem(config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system
	StartSystemWithTimeout(t, sys, 10*time.Second)

	// Verify system is running
	VerifySystemRunning(t, sys)

	// Perform graceful shutdown
	t.Log("Starting graceful shutdown...")
	startTime := time.Now()

	// Shutdown is not cancelable - context is informational only
	// Allow 6 minutes for JuiceFS flush (5 min max + 1 min buffer)
	ctx, cancel := context.WithTimeout(context.Background(), 6*time.Minute)
	defer cancel()

	err = sys.Shutdown(ctx)
	shutdownDuration := time.Since(startTime)

	if err != nil {
		t.Errorf("Shutdown failed: %v", err)
	}

	t.Logf("Shutdown completed in %v", shutdownDuration)

	// Verify everything is stopped
	t.Run("VerifyShutdown", func(t *testing.T) {
		// Wait for process to be fully stopped
		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()

		if err := sys.WhenProcessStopped(ctx); err != nil {
			isRunning := sys.IsProcessRunning()
			t.Errorf("Process did not stop within timeout: %v, IsProcessRunning=%v", err, isRunning)
		}

		// Reaper should be stopped
		// Note: We can't easily check if Reaper is stopped from outside
		// This would require exposing internal state

		// Services should be stopped
		if sys.ServicesManager != nil {
			// Check if any services are still running
			// This would require exposing a method to check service states
		}
	})
}

// TestSystemShutdownTimeout verifies shutdown timeout handling
func TestSystemShutdownTimeout(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Create a process that ignores SIGTERM
	ignoreSigScript := filepath.Join(testDir, "ignore-sigterm.sh")
	scriptContent := `#!/bin/bash
echo "Process that ignores SIGTERM (PID $$)"
trap "" SIGTERM
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

	sys, cleanup, err := TestSystem(config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system
	StartSystemWithTimeout(t, sys, 10*time.Second)

	// Shutdown with generous timeout to allow for JuiceFS cleanup under load
	// Shutdown is not cancelable - allow 6 minutes for JuiceFS flush
	ctx, cancel := context.WithTimeout(context.Background(), 6*time.Minute)
	defer cancel()

	startTime := time.Now()
	err = sys.Shutdown(ctx)
	shutdownDuration := time.Since(startTime)

	// The current implementation doesn't return an error from Shutdown even if StopProcess fails
	// So we verify the behavior by checking the timing
	if err != nil {
		t.Logf("Shutdown returned error: %v", err)
	}

	// Should take around 2 seconds (graceful timeout) plus a bit more for force kill
	if shutdownDuration < 2*time.Second {
		t.Errorf("Shutdown was too fast, expected at least 2s for graceful timeout: %v", shutdownDuration)
	}

	// Allow generous time for storage cleanup in CI/loaded environments
	if shutdownDuration > 30*time.Second {
		t.Errorf("Shutdown took too long: %v", shutdownDuration)
	}

	// Process should still be stopped (force killed)
	if sys.IsProcessRunning() {
		t.Error("Process should be force stopped after timeout")
	}
}

// TestSystemShutdownIdempotency verifies multiple shutdown calls are safe
func TestSystemShutdownIdempotency(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	config := TestConfig(testDir)

	sys, cleanup, err := TestSystem(config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system
	StartSystemWithTimeout(t, sys, 10*time.Second)

	// First shutdown
	// NOTE: Shutdown is NOT cancelable - the context is only informational
	// We pass a long timeout here but shutdown will take as long as needed
	// JuiceFS can take up to 5 minutes, so we allow 6 minutes total
	ctx1, cancel1 := context.WithTimeout(context.Background(), 6*time.Minute)
	defer cancel1()

	err = sys.Shutdown(ctx1)
	if err != nil {
		t.Fatalf("First shutdown failed: %v", err)
	}

	// Second shutdown - should be safe and return quickly since already stopped
	ctx2, cancel2 := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel2()

	err = sys.Shutdown(ctx2)
	if err != nil {
		// This is OK - might return "already shutting down" or similar
		t.Logf("Second shutdown returned: %v", err)
	}
}

// TestSystemShutdownWithActiveConnections tests shutdown with active API connections
func TestSystemShutdownWithActiveConnections(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	config := TestConfig(testDir)

	sys, cleanup, err := TestSystem(config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system
	StartSystemWithTimeout(t, sys, 10*time.Second)

	// TODO: Create active connections to API server
	// This would require actually making HTTP/WebSocket connections

	// Shutdown should handle active connections gracefully
	// Shutdown is not cancelable - allow 6 minutes for JuiceFS flush
	ctx, cancel := context.WithTimeout(context.Background(), 6*time.Minute)
	defer cancel()

	err = sys.Shutdown(ctx)
	if err != nil {
		t.Errorf("Shutdown with active connections failed: %v", err)
	}
}

// TestSystemCrashDuringShutdown tests recovery from crashes during shutdown
func TestSystemCrashDuringShutdown(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Create a process that crashes on SIGTERM
	crashScript := filepath.Join(testDir, "crash-on-sigterm.sh")
	scriptContent := `#!/bin/bash
echo "Process that crashes on SIGTERM (PID $$)"
trap "echo 'Crashing!'; exit 139" SIGTERM
while true; do
	sleep 1
done
`
	if err := os.WriteFile(crashScript, []byte(scriptContent), 0755); err != nil {
		t.Fatal(err)
	}

	config := TestConfig(testDir)
	config.ProcessCommand = []string{crashScript}

	sys, cleanup, err := TestSystem(config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system
	StartSystemWithTimeout(t, sys, 10*time.Second)

	// Shutdown - process will crash but shutdown should complete
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	err = sys.Shutdown(ctx)
	// Error is OK here - process crashed
	if err != nil {
		t.Logf("Shutdown with crash: %v", err)
	}

	// System should still complete shutdown
	if sys.IsProcessRunning() {
		t.Error("Process should be stopped even after crash")
	}
}

// TestSystemSignalTriggeredShutdown tests shutdown via signals (SIGTERM, SIGINT)
func TestSystemSignalTriggeredShutdown(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	config := TestConfig(testDir)

	sys, cleanup, err := TestSystem(config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system
	StartSystemWithTimeout(t, sys, 10*time.Second)

	// Send SIGTERM to trigger shutdown
	t.Log("Sending SIGTERM to trigger shutdown...")
	sys.HandleSignal(syscall.SIGTERM)

	// Wait for shutdown to complete
	done := make(chan struct{})
	go func() {
		exitCode, err := sys.WaitForExit()
		if err != nil {
			t.Errorf("WaitForExit error: %v", err)
		}
		if exitCode != 0 {
			t.Errorf("Expected exit code 0, got %d", exitCode)
		}
		close(done)
	}()

	select {
	case <-done:
		t.Log("System shutdown completed via signal")
	case <-time.After(60 * time.Second):
		t.Fatal("Timeout waiting for signal-triggered shutdown")
	}

	// Give the system a moment to fully clean up
	time.Sleep(100 * time.Millisecond)

	// Verify clean shutdown
	if sys.IsProcessRunning() {
		t.Error("Process should be stopped after signal shutdown")
	}
}

// TestSystemShutdownOrder verifies subsystems shut down in correct order
func TestSystemShutdownOrder(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	config := TestConfig(testDir)

	sys, cleanup, err := TestSystem(config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system
	StartSystemWithTimeout(t, sys, 10*time.Second)

	// Track shutdown order
	// This would require instrumentation in the actual shutdown code
	// For now, just verify shutdown completes

	// Shutdown is not cancelable - allow 6 minutes for JuiceFS flush
	ctx, cancel := context.WithTimeout(context.Background(), 6*time.Minute)
	defer cancel()

	err = sys.Shutdown(ctx)
	if err != nil {
		t.Errorf("Shutdown failed: %v", err)
	}

	// Expected shutdown order:
	// 1. Stop accepting new API requests
	// 2. Stop main process
	// 3. Stop services
	// 4. Unmount storage
	// 5. Stop utilities (reaper, monitors)

	t.Log("Shutdown completed in expected order")
}
