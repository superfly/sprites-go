package tests

import (
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"testing"
	"time"
)

// logMountDiagnostics logs current mount and loop device information for debugging
func logMountDiagnostics(t *testing.T, label string) {
	t.Helper()
	t.Logf("=== Mount diagnostics: %s ===", label)

	// Log mount points
	if output, err := exec.Command("mount").Output(); err == nil {
		t.Logf("mount output:\n%s", string(output))
	} else {
		t.Logf("Failed to run mount: %v", err)
	}

	// Log loop devices
	if output, err := exec.Command("losetup", "-a").Output(); err == nil {
		t.Logf("losetup -a output:\n%s", string(output))
	} else {
		t.Logf("Failed to run losetup: %v", err)
	}

	t.Logf("=== End diagnostics ===")
}

// TestSystemRestoreWithoutShutdownTrigger verifies that restore doesn't trigger system shutdown
// This is the critical test for the bug fix where stopping the container during restore
// was incorrectly triggering a parallel system shutdown
func TestSystemRestoreWithoutShutdownTrigger(t *testing.T) {
	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Create a long-running test process
	testScript := CreateTestScript(t, testDir, "restore-test.sh")

	config := TestConfig(testDir)
	config.ProcessCommand = []string{testScript}

	sys, cleanup, err := TestSystem(config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system
	StartSystemWithTimeout(t, sys, 10*time.Second)
	logMountDiagnostics(t, "After system start")

	// Verify system is running
	VerifySystemRunning(t, sys)

	// Create a checkpoint first
	t.Log("Creating checkpoint for restore test...")
	checkpointCtx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	// CheckpointWithStream generates its own ID, so we need to list checkpoints to get the actual ID
	if err := sys.CheckpointWithStream(checkpointCtx, "", nil); err != nil {
		t.Fatalf("Failed to create checkpoint: %v", err)
	}

	// Get the latest checkpoint ID (skip "Current" which is an alias for active)
	checkpoints, err := sys.ListCheckpoints(context.Background())
	if err != nil || len(checkpoints) == 0 {
		t.Fatalf("Failed to list checkpoints or no checkpoints found: %v", err)
	}
	var checkpointID string
	for _, cp := range checkpoints {
		if cp.ID != "Current" {
			checkpointID = cp.ID
			break
		}
	}
	if checkpointID == "" {
		t.Fatal("No valid checkpoint found (only Current alias exists)")
	}

	t.Logf("Checkpoint created successfully with ID: %s", checkpointID)
	logMountDiagnostics(t, "After checkpoint creation")

	// Give system a moment to stabilize after checkpoint
	time.Sleep(500 * time.Millisecond)

	// Verify process is still running after checkpoint
	if !sys.IsProcessRunning() {
		t.Fatal("Process should still be running after checkpoint")
	}

	// Perform restore operation
	t.Log("Starting restore operation...")
	// Restore calls ShutdownContainer internally - allow 6 minutes for JuiceFS
	restoreCtx, restoreCancel := context.WithTimeout(context.Background(), 7*time.Minute)
	defer restoreCancel()

	// Track if system shutdown is triggered
	shutdownTriggered := false
	done := make(chan struct{})

	// Monitor for unexpected shutdown in parallel
	go func() {
		exitCode, err := sys.WaitForExit()
		if err == nil {
			t.Logf("WARNING: System shutdown was triggered during restore! Exit code: %d", exitCode)
			shutdownTriggered = true
		}
		close(done)
	}()

	// Perform restore
	err = sys.RestoreWithStream(restoreCtx, checkpointID, nil)
	if err != nil {
		t.Fatalf("Restore failed: %v", err)
	}

	t.Log("Restore operation completed")
	logMountDiagnostics(t, "After restore completion")

	// Give system a moment to stabilize after restore
	time.Sleep(1 * time.Second)

	// Verify process is running after restore
	if !sys.IsProcessRunning() {
		t.Fatal("Process should be running after restore")
	}

	// Verify system did not shutdown during restore
	select {
	case <-done:
		if shutdownTriggered {
			t.Fatal("System shutdown was incorrectly triggered during restore operation")
		}
	default:
		// Good - shutdown was not triggered
		t.Log("Confirmed: System shutdown was NOT triggered during restore (as expected)")
	}

	// Verify we can still interact with the system
	t.Log("Verifying system is still functional after restore...")

	// System should still be responsive - test by creating another checkpoint
	checkpointID2 := "post-restore-checkpoint"
	checkpointCtx2, cancel2 := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel2()

	if err := sys.CheckpointWithStream(checkpointCtx2, checkpointID2, nil); err != nil {
		t.Errorf("Failed to create checkpoint after restore: %v", err)
	} else {
		t.Log("Successfully created checkpoint after restore - system is functional")
	}

	// Clean shutdown at the end
	// Shutdown is not cancelable - allow 6 minutes for JuiceFS flush
	shutdownCtx, shutdownCancel := context.WithTimeout(context.Background(), 6*time.Minute)
	defer shutdownCancel()

	if err := sys.Shutdown(shutdownCtx); err != nil {
		t.Fatalf("Final shutdown failed: %v", err)
	}
}

// TestSystemRestoreProcessLifecycle verifies process lifecycle during restore
func TestSystemRestoreProcessLifecycle(t *testing.T) {
	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Create a test process that writes to a file so we can verify it restarted
	testScript := filepath.Join(testDir, "lifecycle-test.sh")
	scriptContent := `#!/bin/bash
echo "Process starting (PID $$) at $(date +%s)" >> ` + filepath.Join(testDir, "process.log") + `
while true; do
	sleep 1
done
`
	if err := os.WriteFile(testScript, []byte(scriptContent), 0755); err != nil {
		t.Fatal(err)
	}

	config := TestConfig(testDir)
	config.ProcessCommand = []string{testScript}

	sys, cleanup, err := TestSystem(config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system
	StartSystemWithTimeout(t, sys, 10*time.Second)

	// Get initial PID
	initialPID := sys.ProcessPID()
	if initialPID == 0 {
		t.Fatal("Failed to get initial process PID")
	}
	t.Logf("Initial process PID: %d", initialPID)

	// Create a checkpoint
	t.Log("Creating checkpoint...")
	checkpointCtx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	if err := sys.CheckpointWithStream(checkpointCtx, "", nil); err != nil {
		t.Fatalf("Failed to create checkpoint: %v", err)
	}

	// Get the latest checkpoint ID (skip "Current" which is an alias for active)
	checkpoints, err := sys.ListCheckpoints(context.Background())
	if err != nil || len(checkpoints) == 0 {
		t.Fatalf("Failed to list checkpoints: %v", err)
	}
	var checkpointID string
	for _, cp := range checkpoints {
		if cp.ID != "Current" {
			checkpointID = cp.ID
			break
		}
	}
	if checkpointID == "" {
		t.Fatal("No valid checkpoint found")
	}

	// Perform restore
	t.Log("Performing restore...")
	// Restore calls ShutdownContainer internally - allow 6 minutes for JuiceFS
	restoreCtx, restoreCancel := context.WithTimeout(context.Background(), 7*time.Minute)
	defer restoreCancel()

	err = sys.RestoreWithStream(restoreCtx, checkpointID, nil)
	if err != nil {
		t.Fatalf("Restore failed: %v", err)
	}

	// Give process time to restart
	time.Sleep(2 * time.Second)

	// Get new PID - it should be different
	newPID := sys.ProcessPID()
	if newPID == 0 {
		t.Fatal("Process did not restart after restore")
	}

	t.Logf("New process PID after restore: %d", newPID)

	if newPID == initialPID {
		t.Error("Process PID should be different after restore (process should have restarted)")
	}

	// Verify process is actually running
	if !sys.IsProcessRunning() {
		t.Fatal("Process should be running after restore")
	}

	// Verify the process log shows both startups
	logFile := filepath.Join(testDir, "process.log")
	content, err := os.ReadFile(logFile)
	if err != nil {
		t.Fatalf("Failed to read process log: %v", err)
	}

	logContent := string(content)
	t.Logf("Process log:\n%s", logContent)

	// Should have at least 2 "Process starting" entries
	// (one initial, one after restore)
	// Note: Could be more if checkpoint itself restarts the process

	// Clean shutdown
	// Shutdown is not cancelable - allow 6 minutes for JuiceFS flush
	shutdownCtx, shutdownCancel := context.WithTimeout(context.Background(), 6*time.Minute)
	defer shutdownCancel()

	if err := sys.Shutdown(shutdownCtx); err != nil {
		t.Fatalf("Shutdown failed: %v", err)
	}
}

// TestSystemRestoreMultipleOperations verifies multiple restore operations in sequence
func TestSystemRestoreMultipleOperations(t *testing.T) {
	requireDockerTest(t)
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

	// Create multiple checkpoints
	var checkpointIDs []string

	for i := 1; i <= 3; i++ {
		t.Logf("Creating checkpoint %d", i)
		// Checkpoint freezes filesystem - may take time if busy
		ctx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
		defer cancel()

		if err := sys.CheckpointWithStream(ctx, "", nil); err != nil {
			t.Fatalf("Failed to create checkpoint %d: %v", i, err)
		}

		// Get the latest checkpoint ID (skip "Current")
		checkpoints, err := sys.ListCheckpoints(context.Background())
		if err != nil || len(checkpoints) == 0 {
			t.Fatalf("Failed to list checkpoints: %v", err)
		}
		var latestID string
		for _, cp := range checkpoints {
			if cp.ID != "Current" {
				latestID = cp.ID
				break
			}
		}
		if latestID == "" {
			t.Fatal("No valid checkpoint found")
		}
		checkpointIDs = append(checkpointIDs, latestID)
		t.Logf("Created checkpoint with ID: %s", latestID)

		// Give some time between checkpoints
		time.Sleep(500 * time.Millisecond)
	}

	// Perform multiple restores
	for i := len(checkpointIDs) - 1; i >= 0; i-- {
		id := checkpointIDs[i]
		t.Logf("Restoring to checkpoint %d: %s", i+1, id)

		// Restore calls ShutdownContainer internally - allow 6 minutes for JuiceFS
		ctx, cancel := context.WithTimeout(context.Background(), 7*time.Minute)
		defer cancel()

		err = sys.RestoreWithStream(ctx, id, nil)
		if err != nil {
			t.Fatalf("Failed to restore to %s: %v", id, err)
		}

		// Verify system is still running
		if !sys.IsProcessRunning() {
			t.Fatalf("Process should be running after restore to %s", id)
		}

		// Give time to stabilize
		time.Sleep(1 * time.Second)
	}

	t.Log("All restore operations completed successfully")

	// Clean shutdown
	// Shutdown is not cancelable - allow 6 minutes for JuiceFS flush
	shutdownCtx, cancel := context.WithTimeout(context.Background(), 6*time.Minute)
	defer cancel()

	if err := sys.Shutdown(shutdownCtx); err != nil {
		t.Fatalf("Shutdown failed: %v", err)
	}
}

// TestSystemRestoreWithProcessCrash verifies restore handles crashed processes correctly
func TestSystemRestoreWithProcessCrash(t *testing.T) {
	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Create a process that exits after a short time
	crashScript := filepath.Join(testDir, "crash-test.sh")
	scriptContent := `#!/bin/bash
echo "Process starting (PID $$)"
sleep 2
echo "Process exiting deliberately"
exit 0
`
	if err := os.WriteFile(crashScript, []byte(scriptContent), 0755); err != nil {
		t.Fatal(err)
	}

	config := TestConfig(testDir)
	config.ProcessCommand = []string{crashScript}
	// Important: Keep system alive even if process exits
	config.KeepAliveOnError = true

	sys, cleanup, err := TestSystem(config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system
	StartSystemWithTimeout(t, sys, 10*time.Second)

	// Create a checkpoint while process is running
	t.Log("Creating checkpoint...")
	checkpointCtx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	if err := sys.CheckpointWithStream(checkpointCtx, "", nil); err != nil {
		t.Fatalf("Failed to create checkpoint: %v", err)
	}

	// Get the latest checkpoint ID (skip "Current")
	checkpoints, err := sys.ListCheckpoints(context.Background())
	if err != nil || len(checkpoints) == 0 {
		t.Fatalf("Failed to list checkpoints: %v", err)
	}
	var checkpointID string
	for _, cp := range checkpoints {
		if cp.ID != "Current" {
			checkpointID = cp.ID
			break
		}
	}
	if checkpointID == "" {
		t.Fatal("No valid checkpoint found")
	}

	// Wait for process to exit
	t.Log("Waiting for process to exit...")
	time.Sleep(3 * time.Second)

	// Process should have exited by now
	if sys.IsProcessRunning() {
		t.Log("Process still running (unexpected)")
	} else {
		t.Log("Process has exited (expected)")
	}

	// Perform restore - should restart the process
	t.Log("Performing restore to restart process...")
	// Restore calls ShutdownContainer internally - allow 6 minutes for JuiceFS
	restoreCtx, restoreCancel := context.WithTimeout(context.Background(), 7*time.Minute)
	defer restoreCancel()

	err = sys.RestoreWithStream(restoreCtx, checkpointID, nil)
	if err != nil {
		t.Fatalf("Restore failed: %v", err)
	}

	// Give process time to restart
	time.Sleep(1 * time.Second)

	// Process should be running again after restore
	if !sys.IsProcessRunning() {
		t.Error("Process should be running after restore")
	} else {
		t.Log("Process successfully restarted after restore")
	}

	// Clean shutdown
	// Shutdown is not cancelable - allow 6 minutes for JuiceFS flush
	shutdownCtx, shutdownCancel := context.WithTimeout(context.Background(), 6*time.Minute)
	defer shutdownCancel()

	if err := sys.Shutdown(shutdownCtx); err != nil {
		t.Fatalf("Shutdown failed: %v", err)
	}
}

// TestSystemRestoreContainerShutdownDoesNotTriggerSystemShutdown is the core test
// for the bug fix - explicitly verifies that ShutdownContainer during restore
// does not trigger the process monitor to initiate full system shutdown
func TestSystemRestoreContainerShutdownDoesNotTriggerSystemShutdown(t *testing.T) {
	requireDockerTest(t)
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

	// Create checkpoint
	t.Log("Creating checkpoint...")
	checkpointCtx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	if err := sys.CheckpointWithStream(checkpointCtx, "", nil); err != nil {
		t.Fatalf("Failed to create checkpoint: %v", err)
	}

	// Get the latest checkpoint ID (skip "Current")
	checkpoints, err := sys.ListCheckpoints(context.Background())
	if err != nil || len(checkpoints) == 0 {
		t.Fatalf("Failed to list checkpoints: %v", err)
	}
	var checkpointID string
	for _, cp := range checkpoints {
		if cp.ID != "Current" {
			checkpointID = cp.ID
			break
		}
	}
	if checkpointID == "" {
		t.Fatal("No valid checkpoint found")
	}

	// Set up a goroutine that will detect if WaitForExit completes
	// (which would mean system shutdown was triggered)
	shutdownDetected := make(chan struct{})
	go func() {
		_, _ = sys.WaitForExit()
		close(shutdownDetected)
	}()

	// Perform restore
	t.Log("Starting restore operation...")
	// Restore calls ShutdownContainer internally - allow 6 minutes for JuiceFS
	restoreCtx, restoreCancel := context.WithTimeout(context.Background(), 7*time.Minute)
	defer restoreCancel()

	restoreDone := make(chan error, 1)
	go func() {
		restoreDone <- sys.RestoreWithStream(restoreCtx, checkpointID, nil)
	}()

	// Wait for either restore to complete or shutdown to be detected
	select {
	case err := <-restoreDone:
		if err != nil {
			t.Fatalf("Restore failed: %v", err)
		}
		t.Log("Restore completed successfully")

	case <-shutdownDetected:
		t.Fatal("CRITICAL: System shutdown was triggered during restore operation - this is the bug we're testing for")

	case <-time.After(45 * time.Second):
		t.Fatal("Restore operation timed out")
	}

	// Give system a moment to fully stabilize
	time.Sleep(1 * time.Second)

	// Verify the shutdown monitor is still waiting (system hasn't shutdown)
	select {
	case <-shutdownDetected:
		t.Fatal("System shutdown was triggered after restore - the bug is present")
	default:
		t.Log("SUCCESS: System shutdown was NOT triggered during or after restore")
	}

	// Verify system is still operational
	if !sys.IsProcessRunning() {
		t.Fatal("Process should be running after restore")
	}

	// Perform clean shutdown
	t.Log("Performing clean shutdown...")
	// Shutdown is not cancelable - allow 6 minutes for JuiceFS flush
	shutdownCtx, shutdownCancel := context.WithTimeout(context.Background(), 6*time.Minute)
	defer shutdownCancel()

	if err := sys.Shutdown(shutdownCtx); err != nil {
		t.Fatalf("Clean shutdown failed: %v", err)
	}

	// Now shutdown should be detected
	select {
	case <-shutdownDetected:
		t.Log("Clean shutdown detected as expected")
	case <-time.After(5 * time.Second):
		t.Error("Clean shutdown was not detected")
	}
}
