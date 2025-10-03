package tests

import (
	"os"
	"path/filepath"
	"syscall"
	"testing"
	"time"

	"github.com/superfly/sprite-env/server/system"
)

// TestSystemShutdownBehavior verifies that the shutdown sequence works correctly
// This is a simpler test that focuses on the shutdown behavior without complex startup scenarios
func TestSystemShutdownBehavior(t *testing.T) {
	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Create a simple test script that runs for a while
	testScript := CreateTestScript(t, testDir, "shutdown-behavior-test.sh")

	config := TestConfig(testDir)
	config.ProcessCommand = []string{testScript}

	sys, err := system.New(config)
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}
	RegisterSystemCleanup(t, sys)

	// Start the system
	StartSystemWithTimeout(t, sys, 30*time.Second)

	// Verify system is running
	VerifySystemRunning(t, sys)

	// Test manual shutdown trigger
	t.Log("Testing manual shutdown trigger...")
	sys.HandleSignal(syscall.SIGTERM)

	// Wait for shutdown to complete
	done := make(chan struct{})
	go func() {
		exitCode, shutdownErr := sys.WaitForExit()
		if shutdownErr != nil {
			t.Errorf("WaitForExit error: %v", shutdownErr)
		}
		t.Logf("System shutdown completed with exit code: %d", exitCode)
		close(done)
	}()

	select {
	case <-done:
		t.Log("System shutdown completed successfully")
	case <-time.After(60 * time.Second):
		t.Fatal("Timeout waiting for shutdown")
	}

	// Verify system is properly shut down
	if sys.IsProcessRunning() {
		t.Error("Process should not be running after shutdown")
	}
}

// TestSystemShutdownOnProcessExit verifies that shutdown sequence runs when process exits unexpectedly
func TestSystemShutdownOnProcessExit(t *testing.T) {
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

	config := TestConfig(testDir)
	config.ProcessCommand = []string{shortRunScript}
	config.KeepAliveOnError = false // Ensure shutdown is triggered on process exit

	sys, err := system.New(config)
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system successfully
	t.Log("Starting system with short-running process...")
	StartSystemWithTimeout(t, sys, 30*time.Second)

	// Verify system is running initially
	VerifySystemRunning(t, sys)

	// Wait for the process to exit and trigger shutdown
	t.Log("Waiting for process to exit and trigger shutdown...")
	done := make(chan struct{})
	go func() {
		exitCode, shutdownErr := sys.WaitForExit()
		if shutdownErr != nil {
			t.Errorf("WaitForExit error: %v", shutdownErr)
		}
		// The exit code should be the process exit code (42)
		if exitCode != 42 {
			t.Errorf("Expected exit code 42, got %d", exitCode)
		}
		t.Logf("System shutdown completed with exit code: %d", exitCode)
		close(done)
	}()

	select {
	case <-done:
		t.Log("System shutdown completed after unexpected process exit")
	case <-time.After(60 * time.Second):
		t.Fatal("Timeout waiting for shutdown after process exit")
	}

	// Verify system is properly shut down
	if sys.IsProcessRunning() {
		t.Error("Process should not be running after unexpected exit and shutdown")
	}
}

// TestSystemKeepAliveOnError verifies that KeepAliveOnError prevents shutdown on process exit
func TestSystemKeepAliveOnError(t *testing.T) {
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

	sys, err := system.New(config)
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system successfully
	t.Log("Starting system with KeepAliveOnError enabled...")
	StartSystemWithTimeout(t, sys, 30*time.Second)

	// Verify system is running initially
	VerifySystemRunning(t, sys)

	// Wait for the process to exit
	t.Log("Waiting for process to exit...")
	WaitForCondition(t, 10*time.Second, 100*time.Millisecond, func() bool {
		return !sys.IsProcessRunning()
	}, "process to exit")

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

	done := make(chan struct{})
	go func() {
		exitCode, shutdownErr := sys.WaitForExit()
		if shutdownErr != nil {
			t.Errorf("WaitForExit error: %v", shutdownErr)
		}
		t.Logf("Manual shutdown completed with exit code: %d", exitCode)
		close(done)
	}()

	select {
	case <-done:
		t.Log("Manual shutdown completed successfully")
	case <-time.After(60 * time.Second):
		t.Fatal("Timeout waiting for manual shutdown")
	}
}
