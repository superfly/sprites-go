package tests

import (
	"context"
	"os"
	"path/filepath"
	"syscall"
	"testing"
	"time"
)

// TestSystemShutdownBehavior verifies that the shutdown sequence works correctly
// This is a simpler test that focuses on the shutdown behavior without complex startup scenarios
func TestSystemShutdownBehavior(t *testing.T) {
	_, cancel := SetTestDeadline(t)
	defer cancel()

	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Create a simple test script that runs for a while
	testScript := CreateTestScript(t, testDir, "shutdown-behavior-test.sh")

	config := TestConfig(testDir)
	config.ProcessCommand = []string{testScript}

	sys, cleanup, err := TestSystem(t, config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system
	if err := sys.Start(); err != nil {
		t.Fatalf("Failed to start system: %v", err)
	}

	// Start WaitForExit in background (mimics production main.go)
	// This waits for shutdownTriggeredCh to close, then calls Shutdown()
	go func() {
		exitCode, err := sys.WaitForExit()
		if err != nil {
			t.Logf("WaitForExit error: %v", err)
		}
		t.Logf("WaitForExit completed with exit code: %d", exitCode)
	}()

	// Test manual shutdown trigger via signal
	// Flow: HandleSignal forwards SIGTERM to process → process exits →
	//       monitorProcessLoop detects exit → closes shutdownTriggeredCh →
	//       WaitForExit calls Shutdown() → process stops completely
	t.Log("Testing manual shutdown trigger via signal...")

	// Start a goroutine to monitor the process PID
	pid := sys.ProcessPID()
	t.Logf("Process PID: %d", pid)
	done := make(chan struct{})
	go func() {
		defer close(done)
		for i := 0; i < 60; i++ {
			time.Sleep(1 * time.Second)

			// Check if PID still exists
			err := syscall.Kill(pid, 0)
			isRunning := sys.IsProcessRunning()
			currentPID := sys.ProcessPID()

			if err != nil {
				t.Logf("[%ds] PID %d check: syscall.Kill returned error: %v, IsProcessRunning=%v, CurrentPID=%d",
					i+1, pid, err, isRunning, currentPID)
			} else {
				t.Logf("[%ds] PID %d still exists, IsProcessRunning=%v, CurrentPID=%d",
					i+1, pid, isRunning, currentPID)
			}

			if !isRunning && currentPID == 0 {
				t.Logf("[%ds] Process stopped according to system state", i+1)
				return
			}
		}
		t.Logf("Monitor goroutine timed out after 60 seconds")
	}()

	sys.HandleSignal(syscall.SIGTERM)

	// Wait for shutdown to complete with a timeout
	ctx, cancel := context.WithTimeout(t.Context(), 10*time.Second)
	defer cancel()
	if err := sys.WhenProcessStopped(ctx); err != nil {
		t.Fatalf("Process did not stop: %v", err)
	}

	<-done // Wait for monitor goroutine to finish
}

// TestSystemShutdownOnProcessExit verifies that shutdown sequence runs when process exits unexpectedly
func TestSystemShutdownOnProcessExit(t *testing.T) {
	_, cancel := SetTestDeadline(t)
	defer cancel()

	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Create a script that runs for a short time then exits
	shortRunScript := filepath.Join(testDir, "short-run.sh")
	scriptContent := `#!/bin/bash
echo "Process starting (PID $$)"
sleep 2
echo "Process exiting unexpectedly"
exit 42
`
	if err := os.WriteFile(shortRunScript, []byte(scriptContent), 0755); err != nil {
		t.Fatal(err)
	}

	config := VerboseTestConfig(testDir) // Use verbose logging to debug exit code
	config.ProcessCommand = []string{shortRunScript}
	config.KeepAliveOnError = false // Ensure shutdown is triggered on process exit

	sys, cleanup, err := TestSystem(t, config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system successfully
	t.Log("Starting system with short-running process...")
	if err := sys.Start(); err != nil {
		t.Fatalf("Failed to start system: %v", err)
	}

	// Wait for the process to exit and trigger shutdown
	t.Log("Waiting for process to exit and trigger shutdown...")
	if err := sys.WhenProcessStopped(t.Context()); err != nil {
		t.Fatalf("Process did not stop: %v", err)
	}

	// Verify exit code
	if sys.GetProcessExitCode() != 42 {
		t.Errorf("Expected exit code 42, got %d", sys.GetProcessExitCode())
	}
}

// TestSystemKeepAliveOnError verifies that KeepAliveOnError prevents shutdown on process exit
func TestSystemKeepAliveOnError(t *testing.T) {
	_, cancel := SetTestDeadline(t)
	defer cancel()

	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Create a script that runs for a short time then exits
	shortRunScript := filepath.Join(testDir, "short-run-keepalive.sh")
	scriptContent := `#!/bin/bash
echo "Process starting (PID $$)"
sleep 2
echo "Process exiting but server should keep running"
exit 1
`
	if err := os.WriteFile(shortRunScript, []byte(scriptContent), 0755); err != nil {
		t.Fatal(err)
	}

	config := TestConfig(testDir)
	config.ProcessCommand = []string{shortRunScript}
	config.KeepAliveOnError = true // Keep server alive when process exits

	sys, cleanup, err := TestSystem(t, config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system successfully
	t.Log("Starting system with KeepAliveOnError enabled...")
	if err := sys.Start(); err != nil {
		t.Fatalf("Failed to start system: %v", err)
	}

	// Wait for the process to exit
	t.Log("Waiting for process to exit...")

	if err := sys.WhenProcessStopped(t.Context()); err != nil {
		t.Fatalf("Process did not stop: %v", err)
	}

	// Wait a bit more to ensure shutdown is not triggered
	time.Sleep(2 * time.Second)

	// Verify system is still running (not shut down)
	// The API server should still be available
	if sys.APIServer == nil {
		t.Error("API server should still be running with KeepAliveOnError")
	}

	// Now manually trigger shutdown
	t.Log("Manually triggering shutdown...")
	sys.HandleSignal(syscall.SIGTERM)
	if err := sys.WhenProcessStopped(t.Context()); err != nil {
		t.Fatalf("Process did not stop: %v", err)
	}

}
