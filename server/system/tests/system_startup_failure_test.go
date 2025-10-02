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

	// Start the system
	StartSystemWithTimeout(t, sys, 10*time.Second)

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
	case <-time.After(10 * time.Second):
		t.Fatal("Timeout waiting for shutdown")
	}

	// Verify system is properly shut down
	if sys.IsProcessRunning() {
		t.Error("Process should not be running after shutdown")
	}
}

// TestSystemShutdownOnStartupFailure verifies that shutdown sequence runs when startup fails
// This test simulates the main.go behavior where sys.Start() fails and triggers shutdown
func TestSystemShutdownOnStartupFailure(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Create a script that exits immediately (simulating process initialization failure)
	failScript := filepath.Join(testDir, "fail-startup.sh")
	scriptContent := `#!/bin/bash
echo "Process exiting immediately to simulate startup failure"
exit 1
`
	if err := os.WriteFile(failScript, []byte(scriptContent), 0755); err != nil {
		t.Fatal(err)
	}

	// Use TestConfig but override the process command
	config := TestConfig(testDir)
	config.ProcessCommand = []string{failScript}

	sys, err := system.New(config)
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system - the process will exit immediately but Start() should succeed
	t.Log("Starting system with process that exits immediately...")

	if err := sys.Start(); err != nil {
		t.Fatalf("System start failed: %v", err)
	}
	t.Log("System started successfully")

	// Give the monitor loop a moment to start watching the process
	time.Sleep(100 * time.Millisecond)

	// Wait for the system to automatically shut down when the process exits
	t.Log("Waiting for automatic shutdown after process exit...")
	done := make(chan struct{})
	go func() {
		exitCode, shutdownErr := sys.WaitForExit()
		if shutdownErr != nil {
			t.Errorf("WaitForExit error: %v", shutdownErr)
		}
		t.Logf("System shutdown completed with exit code: %d", exitCode)
		if exitCode != 1 {
			t.Errorf("Expected exit code 1 from failed process, got %d", exitCode)
		}
		close(done)
	}()

	select {
	case <-done:
		t.Log("System automatically shut down after process exit")
	case <-time.After(10 * time.Second):
		t.Fatal("Timeout waiting for automatic shutdown after process exit")
	}

	// Verify system is properly shut down
	if sys.IsProcessRunning() {
		t.Error("Process should not be running after startup failure and shutdown")
	}
}

// TestSystemShutdownOnProcessExit verifies that shutdown sequence runs when process exits unexpectedly
func TestSystemShutdownOnProcessExit(t *testing.T) {
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
	StartSystemWithTimeout(t, sys, 10*time.Second)

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
	case <-time.After(15 * time.Second):
		t.Fatal("Timeout waiting for shutdown after process exit")
	}

	// Verify system is properly shut down
	if sys.IsProcessRunning() {
		t.Error("Process should not be running after unexpected exit and shutdown")
	}
}

// TestSystemKeepAliveOnError verifies that KeepAliveOnError prevents shutdown on process exit
func TestSystemKeepAliveOnError(t *testing.T) {
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
	StartSystemWithTimeout(t, sys, 10*time.Second)

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
	case <-time.After(10 * time.Second):
		t.Fatal("Timeout waiting for manual shutdown")
	}
}

// TestSystemShutdownOnStorageFailure verifies shutdown behavior when storage components fail
func TestSystemShutdownOnStorageFailure(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Create a read-only directory to cause JuiceFS/overlay failures
	readOnlyDir := filepath.Join(testDir, "readonly")
	if err := os.MkdirAll(readOnlyDir, 0755); err != nil {
		t.Fatal(err)
	}

	// Make the directory read-only
	if err := os.Chmod(readOnlyDir, 0444); err != nil {
		t.Logf("Could not make directory read-only (possibly running as root): %v", err)
		// Skip this test if we can't make it read-only
		t.Skip("Cannot make directory read-only, skipping test")
	}

	config := TestConfig(testDir)
	config.JuiceFSDataPath = readOnlyDir // This should cause JuiceFS to fail

	sys, err := system.New(config)
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Attempt to start the system - this should fail due to storage issues
	t.Log("Attempting to start system with storage failure...")
	err = sys.Start()
	if err == nil {
		t.Fatal("Expected system start to fail due to storage issues, but it succeeded")
	}

	t.Logf("System start failed as expected: %v", err)

	// The system should have triggered shutdown automatically
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
		t.Log("System shutdown completed after storage failure")
	case <-time.After(10 * time.Second):
		t.Fatal("Timeout waiting for shutdown after storage failure")
	}
}

// TestSystemShutdownOnDatabaseFailure verifies shutdown behavior when database fails
func TestSystemShutdownOnDatabaseFailure(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Create a read-only directory for the database
	readOnlyDir := filepath.Join(testDir, "readonly-db")
	if err := os.MkdirAll(readOnlyDir, 0755); err != nil {
		t.Fatal(err)
	}

	// Make the directory read-only
	if err := os.Chmod(readOnlyDir, 0444); err != nil {
		t.Logf("Could not make directory read-only (possibly running as root): %v", err)
		// Skip this test if we can't make it read-only
		t.Skip("Cannot make directory read-only, skipping test")
	}

	config := TestConfig(testDir)
	config.WriteDir = readOnlyDir // This should cause database manager to fail

	sys, err := system.New(config)
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Attempt to start the system - this should fail due to database issues
	t.Log("Attempting to start system with database failure...")
	err = sys.Start()
	if err == nil {
		t.Fatal("Expected system start to fail due to database issues, but it succeeded")
	}

	t.Logf("System start failed as expected: %v", err)

	// The system should have triggered shutdown automatically
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
		t.Log("System shutdown completed after database failure")
	case <-time.After(10 * time.Second):
		t.Fatal("Timeout waiting for shutdown after database failure")
	}
}
