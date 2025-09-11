package portwatcher

import (
	"testing"
	"time"
)

// TestPortWatcherDynamicPIDs tests adding and removing PIDs dynamically
func TestPortWatcherDynamicPIDs(t *testing.T) {
	// Create a simple callback to track port events
	var events []Port
	callback := func(port Port) {
		events = append(events, port)
	}

	// Create port watcher with initial PID (use current process for testing)
	initialPID := 99999 // Non-existent PID for testing
	pw, err := New(initialPID, callback)
	if err != nil {
		t.Fatalf("Failed to create port watcher: %v", err)
	}

	// Verify initial state
	if len(pw.pids) != 1 || pw.pids[0] != initialPID {
		t.Errorf("Expected initial PID %d, got %v", initialPID, pw.pids)
	}

	// Test adding PIDs
	t.Run("AddPID", func(t *testing.T) {
		// Add a new PID
		newPID := 88888
		err := pw.AddPID(newPID)
		if err != nil {
			t.Errorf("Failed to add PID: %v", err)
		}

		// Verify PID was added
		if len(pw.pids) != 2 {
			t.Errorf("Expected 2 PIDs after add, got %d", len(pw.pids))
		}

		// Try adding duplicate PID (should be no-op)
		err = pw.AddPID(newPID)
		if err != nil {
			t.Errorf("Adding duplicate PID should not error: %v", err)
		}
		if len(pw.pids) != 2 {
			t.Errorf("Duplicate PID should not be added, expected 2 PIDs, got %d", len(pw.pids))
		}
	})

	// Test removing PIDs
	t.Run("RemovePID", func(t *testing.T) {
		// Add another PID for testing
		anotherPID := 77777
		pw.AddPID(anotherPID)

		initialCount := len(pw.pids)

		// Remove a PID
		pw.RemovePID(88888)

		if len(pw.pids) != initialCount-1 {
			t.Errorf("Expected %d PIDs after removal, got %d", initialCount-1, len(pw.pids))
		}

		// Remove non-existent PID (should be no-op)
		pw.RemovePID(12345)
		if len(pw.pids) != initialCount-1 {
			t.Errorf("Removing non-existent PID should not change count")
		}
	})

	// Test idle state
	t.Run("IdleState", func(t *testing.T) {
		// Remove all PIDs
		for len(pw.pids) > 0 {
			pw.RemovePID(pw.pids[0])
		}

		if !pw.idle {
			t.Error("PortWatcher should be idle when no PIDs are monitored")
		}

		// Add a PID should make it non-idle
		pw.AddPID(55555)
		if pw.idle {
			t.Error("PortWatcher should not be idle after adding a PID")
		}
	})
}

// TestPortWatcherConcurrentOperations tests thread safety of add/remove operations
func TestPortWatcherConcurrentOperations(t *testing.T) {
	callback := func(port Port) {}
	pw, err := New(11111, callback)
	if err != nil {
		t.Fatalf("Failed to create port watcher: %v", err)
	}

	// Run concurrent add/remove operations
	done := make(chan bool)

	// Goroutine adding PIDs
	go func() {
		for i := 0; i < 100; i++ {
			pw.AddPID(20000 + i)
			time.Sleep(time.Microsecond)
		}
		done <- true
	}()

	// Goroutine removing PIDs
	go func() {
		for i := 0; i < 50; i++ {
			pw.RemovePID(20000 + i*2)
			time.Sleep(time.Microsecond)
		}
		done <- true
	}()

	// Wait for both to complete
	<-done
	<-done

	// Verify state is consistent (no crashes, reasonable PID count)
	if len(pw.pids) < 1 || len(pw.pids) > 101 {
		t.Errorf("Unexpected PID count after concurrent operations: %d", len(pw.pids))
	}
}
