package terminal

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"testing"
	"time"

	"github.com/superfly/sprite-env/pkg/tap"
	"github.com/superfly/sprite-env/pkg/tmux"
)

// Helper to create a test tmux socket for activity tests
func createActivityTestSocket(t *testing.T) string {
	socketPath := fmt.Sprintf("/tmp/tmux-activity-test-%d-%d", os.Getpid(), time.Now().UnixNano())
	t.Cleanup(func() {
		os.Remove(socketPath)
		// Kill any tmux server using this socket
		cmd := exec.Command("tmux", "-S", socketPath, "kill-server")
		cmd.Run()
	})
	return socketPath
}

// Helper to create a tmux session for testing
func createTestSession(t *testing.T, socketPath, sessionName string) {
	cmd := exec.Command("tmux", "-S", socketPath, "new-session", "-d", "-s", sessionName)
	output, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("Failed to create session %s: %v (output: %s)", sessionName, err, string(output))
	}
}

// Helper to send output to a tmux session
func sendOutputToSession(t *testing.T, socketPath, sessionName, text string) {
	cmd := exec.Command("tmux", "-S", socketPath, "send-keys", "-t", sessionName, text, "Enter")
	if err := cmd.Run(); err != nil {
		t.Fatalf("Failed to send output to session %s: %v", sessionName, err)
	}
}

func TestTMUXManager_GetAllSessionActivityInfo_ActiveStatus(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping activity test in short mode")
	}

	socketPath := createActivityTestSocket(t)

	// Use discard logger to suppress output
	logger := tap.NewDiscardLogger()

	// Create context with logger
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)

	// Create window monitor
	// Note: We're testing the window monitor directly since TMUXManager
	// creates its own internal window monitor
	monitorSession := "activity-monitor"
	createTestSession(t, socketPath, monitorSession)

	wm := tmux.NewWindowMonitor(ctx, monitorSession).
		WithSocketPath(socketPath).
		WithConfigPath("").
		WithTmuxBinary("tmux")

	// Start window monitor
	if err := wm.Start(ctx); err != nil {
		t.Fatalf("Failed to start window monitor: %v", err)
	}
	defer wm.Close()

	// Get event channel
	eventChan := wm.GetEventChannel()

	// Give monitor time to initialize
	time.Sleep(100 * time.Millisecond)

	// We can't set the window monitor directly, so we'll just use it to check activity stats
	// The TMUXManager would normally create its own window monitor

	// Create test sessions
	createTestSession(t, socketPath, "sprite-exec-1")
	createTestSession(t, socketPath, "sprite-exec-2")

	// Wait for discovery
	time.Sleep(500 * time.Millisecond)

	// Test 1: Check initial state (should be active as new sessions start active)
	t.Run("NewSessionsStartActive", func(t *testing.T) {
		// Get activity stats directly from window monitor
		activityStats := wm.GetActivityStats()

		if len(activityStats) == 0 {
			t.Log("No sessions discovered yet, waiting...")
			time.Sleep(1 * time.Second)
			activityStats = wm.GetActivityStats()
		}

		// Check that new sessions are marked as active
		for sessionID, stats := range activityStats {
			if !stats.IsActive {
				t.Errorf("Expected new session %s to be active, but it's inactive", sessionID)
			}
			t.Logf("Session %s: IsActive=%v, LastActivity=%v",
				sessionID, stats.IsActive, stats.LastActivity)
		}
	})

	// Test 2: Generate activity and verify it's tracked
	t.Run("ActivityTracking", func(t *testing.T) {
		// Send some output to session 1
		sendOutputToSession(t, socketPath, "sprite-exec-1", "echo 'test activity'")

		// Wait for activity to be processed
		time.Sleep(500 * time.Millisecond)

		activityStats := wm.GetActivityStats()

		if stats, ok := activityStats["1"]; ok {
			if !stats.IsActive {
				t.Error("Expected session 1 to be active after sending output")
			}
			if stats.ByteCount == 0 {
				t.Error("Expected non-zero byte count after activity")
			}
			// Calculate bytes per second
			duration := time.Since(stats.StartTime).Seconds()
			bytesPerSecond := float64(stats.ByteCount) / duration
			t.Logf("Session 1 after activity: IsActive=%v, ByteCount=%v, BytesPerSecond=%v",
				stats.IsActive, stats.ByteCount, bytesPerSecond)
		} else {
			t.Error("Session 1 not found in activity stats")
		}
	})

	// Test 3: Wait for timeout and verify inactive status
	t.Run("InactivityTimeout", func(t *testing.T) {
		// Wait for inactivity timeout (5 seconds + buffer)
		t.Log("Waiting for inactivity timeout...")
		time.Sleep(6 * time.Second)

		activityStats := wm.GetActivityStats()

		if stats, ok := activityStats["1"]; ok {
			if stats.IsActive {
				t.Error("Expected session 1 to be inactive after 5 second timeout")
			}
			t.Logf("Session 1 after timeout: IsActive=%v, LastActivity=%v",
				stats.IsActive, stats.LastActivity)
		} else {
			t.Error("Session 1 not found in activity stats")
		}
	})

	// Test 4: Reactivate and verify status changes
	t.Run("Reactivation", func(t *testing.T) {
		// Send more output to reactivate
		sendOutputToSession(t, socketPath, "sprite-exec-1", "echo 'reactivated'")

		// Wait for activity to be processed
		time.Sleep(500 * time.Millisecond)

		activityStats := wm.GetActivityStats()

		if stats, ok := activityStats["1"]; ok {
			if !stats.IsActive {
				t.Error("Expected session 1 to be active again after new output")
			}
			t.Logf("Session 1 after reactivation: IsActive=%v", stats.IsActive)
		} else {
			t.Error("Session 1 not found in activity stats")
		}
	})

	// Test 5: Check window monitor events
	t.Run("WindowMonitorEvents", func(t *testing.T) {
		// Drain and log any events
		eventCount := 0
		timeout := time.After(100 * time.Millisecond)

	eventLoop:
		for {
			select {
			case event := <-eventChan:
				eventCount++
				t.Logf("Window monitor event: Type=%s, Session=%s",
					event.EventType, event.OriginalSession)
			case <-timeout:
				break eventLoop
			}
		}

		if eventCount == 0 {
			t.Log("Warning: No window monitor events received")
		}
	})
}

func TestTMUXManager_GetAllSessionActivityInfo_EdgeCases(t *testing.T) {
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, tap.NewDiscardLogger())

	// Test without window monitor
	t.Run("NoWindowMonitor", func(t *testing.T) {
		tm := NewTMUXManager(ctx)
		activityInfo := tm.GetAllSessionActivityInfo()

		if len(activityInfo) != 0 {
			t.Errorf("Expected empty activity info without window monitor, got %d entries",
				len(activityInfo))
		}
	})

	// Test that TMUXManager returns empty without window monitor
	t.Run("TMUXManagerWithoutMonitor", func(t *testing.T) {
		tm2 := NewTMUXManager(ctx)
		// Don't set window monitor - it should be nil

		activityInfo := tm2.GetAllSessionActivityInfo()
		if len(activityInfo) != 0 {
			t.Errorf("Expected empty activity info without window monitor, got %d entries",
				len(activityInfo))
		}
	})
}

// Test to verify the exact scenario from the bug report
func TestTMUXManager_GetAllSessionActivityInfo_BugScenario(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping bug scenario test in short mode")
	}

	socketPath := createActivityTestSocket(t)

	// Use discard logger to suppress output
	logger := tap.NewDiscardLogger()

	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)

	// Create window monitor
	// Note: We're testing the window monitor directly
	monitorSession := "bug-monitor"
	createTestSession(t, socketPath, monitorSession)

	wm := tmux.NewWindowMonitor(ctx, monitorSession).
		WithSocketPath(socketPath).
		WithConfigPath("").
		WithTmuxBinary("tmux")

	// Start window monitor
	if err := wm.Start(ctx); err != nil {
		t.Fatalf("Failed to start window monitor: %v", err)
	}
	defer wm.Close()

	// Give monitor time to initialize
	time.Sleep(100 * time.Millisecond)

	// Create session with ID "0" like in the bug report
	createTestSession(t, socketPath, "sprite-exec-0")

	// Send "top" command to match the bug scenario
	sendOutputToSession(t, socketPath, "sprite-exec-0", "top")

	// Wait for discovery and activity processing
	time.Sleep(1 * time.Second)

	// Create TMUXManager to test the mapping
	tm := NewTMUXManager(ctx).WithSocketPath(socketPath).WithConfigPath("").WithTmuxBinary("tmux")

	// Set the window monitor in TMUXManager
	// Note: Normally this is done internally, but for testing we need to set it manually
	tm.windowMonitor = wm

	// Get activity info through TMUXManager - this simulates what the GET /exec endpoint would get
	activityInfo := tm.GetAllSessionActivityInfo()

	// Log the activity info
	t.Logf("Activity info from TMUXManager: %+v", activityInfo)

	// Check if session "0" exists and its status
	if info, ok := activityInfo["0"]; ok {
		t.Logf("Session 0 status: IsActive=%v, BytesPerSecond=%v, LastActivity=%v",
			info.IsActive, info.BytesPerSecond, info.LastActivity)

		// According to the bug, this is showing as inactive when it should be active
		if !info.IsActive && info.BytesPerSecond > 0 {
			t.Error("BUG REPRODUCED: Session is marked inactive but has bytes_per_second > 0")
		}
	} else {
		t.Error("Session 0 not found in activity info")

		// Log all available sessions
		t.Log("Available sessions from TMUXManager:")
		for id, info := range activityInfo {
			t.Logf("  Session %s: %+v", id, info)
		}
	}
}
