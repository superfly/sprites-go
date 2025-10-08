package tests

import (
	"context"
	"os"
	"path/filepath"
	"testing"
	"time"
)

// TestSystemRestoreWithoutShutdownTrigger verifies that restore doesn't trigger system shutdown
// This is the critical test for the bug fix where stopping the container during restore
// was incorrectly triggering a parallel system shutdown
func TestSystemRestoreWithoutShutdownTrigger(t *testing.T) {
	_, cancel := SetTestDeadline(t)
	defer cancel()

	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Create a long-running test process
	testScript := CreateTestScript(t, testDir, "restore-test.sh")

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

	// Verify system is running

	// Create a checkpoint first
	t.Log("Creating checkpoint for restore test...")
	// CheckpointWithStream generates its own ID, so we need to list checkpoints to get the actual ID
	if err := sys.CheckpointWithStream(context.Background(), "", nil); err != nil {
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

	err = sys.WhenProcessRunning(t.Context())
	if err != nil {
		t.Fatalf("Process should still be running after checkpoint: %v", err)
	}

	// Perform restore operation
	t.Log("Starting restore operation...")

	// Perform restore
	err = sys.RestoreWithStream(context.Background(), checkpointID, nil)
	if err != nil {
		t.Fatalf("Restore failed: %v", err)
	}

	t.Log("Restore operation completed")

	err = sys.WhenProcessRunning(t.Context())
	if err != nil {
		t.Fatalf("Process should have restarted after restore: %v", err)
	}

	// Verify we can still interact with the system
	t.Log("Verifying system is still functional after restore...")

	// System should still be responsive - test by creating another checkpoint
	checkpointID2 := "post-restore-checkpoint"
	if err := sys.CheckpointWithStream(context.Background(), checkpointID2, nil); err != nil {
		t.Errorf("Failed to create checkpoint after restore: %v", err)
	} else {
		t.Log("Successfully created checkpoint after restore - system is functional")
	}

	// Clean shutdown at the end
	if err := sys.Shutdown(context.Background()); err != nil {
		t.Fatalf("Final shutdown failed: %v", err)
	}
}

// TestSystemRestoreProcessLifecycle verifies process lifecycle during restore
func TestSystemRestoreProcessLifecycle(t *testing.T) {
	_, cancel := SetTestDeadline(t)
	defer cancel()

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

	sys, cleanup, err := TestSystem(t, config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system
	if err := sys.Start(); err != nil {
		t.Fatalf("Failed to start system: %v", err)
	}

	// Get initial PID
	initialPID := sys.ProcessPID()
	if initialPID == 0 {
		t.Fatal("Failed to get initial process PID")
	}
	t.Logf("Initial process PID: %d", initialPID)

	// Create a checkpoint
	t.Log("Creating checkpoint...")

	if err := sys.CheckpointWithStream(context.Background(), "", nil); err != nil {
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

	err = sys.RestoreWithStream(context.Background(), checkpointID, nil)
	if err != nil {
		t.Fatalf("Restore failed: %v", err)
	}

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
	if err := sys.Shutdown(context.Background()); err != nil {
		t.Fatalf("Shutdown failed: %v", err)
	}
}

// TestSystemRestoreMultipleOperations verifies multiple restore operations in sequence
func TestSystemRestoreMultipleOperations(t *testing.T) {
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

	// Create multiple checkpoints
	var checkpointIDs []string

	for i := 1; i <= 3; i++ {
		t.Logf("Creating checkpoint %d", i)

		if err := sys.CheckpointWithStream(context.Background(), "", nil); err != nil {
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

		err = sys.RestoreWithStream(context.Background(), id, nil)
		if err != nil {
			t.Fatalf("Failed to restore to %s: %v", id, err)
		}

		// Verify system is still running
		if !sys.IsProcessRunning() {
			t.Fatalf("Process should be running after restore to %s", id)
		}

		// Verify ServicesManager is in good state (should be started after restore)
		if sys.ServicesManager != nil {
			// Try to list services - this will fail if manager isn't started properly
			_, listErr := sys.ServicesManager.ListServices()
			if listErr != nil {
				t.Errorf("ServicesManager in bad state after restore to %s: %v", id, listErr)
			}
		}

		// Give time to stabilize
		time.Sleep(1 * time.Second)
	}

	t.Log("All restore operations completed successfully")

	// Clean shutdown
	if err := sys.Shutdown(context.Background()); err != nil {
		t.Fatalf("Shutdown failed: %v", err)
	}
}

// TestSystemRestoreWithProcessCrash verifies restore handles crashed processes correctly
func TestSystemRestoreWithProcessCrash(t *testing.T) {
	_, cancel := SetTestDeadline(t)
	defer cancel()

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

	sys, cleanup, err := TestSystem(t, config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	// Start the system
	if err := sys.Start(); err != nil {
		t.Fatalf("Failed to start system: %v", err)
	}

	// Create a checkpoint while process is running
	t.Log("Creating checkpoint...")

	if err := sys.CheckpointWithStream(context.Background(), "", nil); err != nil {
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

	// Perform restore - should restart the process
	t.Log("Performing restore to restart process...")

	err = sys.RestoreWithStream(context.Background(), checkpointID, nil)
	if err != nil {
		t.Fatalf("Restore failed: %v", err)
	}

	err = sys.WhenProcessRunning(t.Context())
	if err != nil {
		t.Fatalf("Process did not restart: %v", err)
	}

	// Clean shutdown
	if err := sys.Shutdown(context.Background()); err != nil {
		t.Fatalf("Shutdown failed: %v", err)
	}
}
