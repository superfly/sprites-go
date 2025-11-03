package tmux

import (
	"context"
	"os/exec"
	"testing"
	"time"

	"github.com/superfly/sprite-env/pkg/tap"
)

// TestWindowMonitorUnlinkedWindowOutput tests that when output arrives from an unlinked window,
// it gets linked and generates activity events
func TestWindowMonitorUnlinkedWindowOutput(t *testing.T) {
	socketPath := createTestSocket(t)
	defer killTmuxServer(socketPath)

	logger := tap.NewDiscardLogger()

	// Create monitor session
	createTmuxSession(t, socketPath, "test-monitor")

	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	wm := NewWindowMonitor(ctx, "test-monitor").
		WithSocketPath(socketPath).
		WithConfigPath("").
		WithCommand(exec.Command("tmux"))

	ctx, cancel := context.WithTimeout(context.Background(), 15*time.Second)
	defer cancel()

	// Start the monitor
	if err := wm.Start(ctx); err != nil {
		t.Fatalf("Failed to start window monitor: %v", err)
	}

	// Wait for monitor to initialize
	time.Sleep(500 * time.Millisecond)

	// Verify no windows are linked yet
	linkedWindows := wm.GetLinkedWindows()
	if len(linkedWindows) != 0 {
		t.Fatalf("Expected 0 linked windows initially, got %d", len(linkedWindows))
	}

	// Create a sprite-exec session AFTER monitor started (so it won't be discovered initially)
	createTmuxSession(t, socketPath, "sprite-exec-999")

	// Important: Don't trigger discovery yet - we want to test on-demand linking

	// Send output to the unlinked session
	// This should trigger linkWindowFromPane when the output event arrives
	t.Log("Sending output to unlinked session...")
	sendKeysToPane(t, socketPath, "sprite-exec-999", "echo 'test from unlinked window'")
	sendKeysToPane(t, socketPath, "sprite-exec-999", "Enter")

	// Wait for the linkWindowFromPane to happen
	time.Sleep(2 * time.Second)

	// Verify the window is now linked
	linkedWindows = wm.GetLinkedWindows()
	if len(linkedWindows) == 0 {
		t.Fatal("Window was not linked after receiving output from unlinked pane")
	}

	t.Logf("Window linked successfully: %d windows linked", len(linkedWindows))

	// Collect events - we should see activity events
	events := make([]WindowMonitorEvent, 0)
	timeout := time.After(3 * time.Second)

collectLoop:
	for {
		select {
		case event := <-wm.GetEventChannel():
			events = append(events, event)
			if event.EventType == "activity" {
				t.Logf("Got activity event: window=%s, session=%s, bytes=%d",
					event.WindowID, event.OriginalSession, len(event.Data))
			}
		case <-timeout:
			break collectLoop
		}
	}

	// Verify we got activity events
	activityEventCount := 0
	for _, event := range events {
		if event.EventType == "activity" {
			activityEventCount++
			// Verify the session ID has the $ prefix (required for activity monitor)
			if event.OriginalSession[0] != '$' {
				t.Errorf("Activity event has incorrect session ID format: %q (expected $-prefix)",
					event.OriginalSession)
			}
		}
	}

	if activityEventCount == 0 {
		t.Error("No activity events received from linked window")
		t.Logf("Total events received: %d", len(events))
		for _, event := range events {
			t.Logf("  Event: type=%s, window=%s, session=%s",
				event.EventType, event.WindowID, event.OriginalSession)
		}
	} else {
		t.Logf("Successfully received %d activity events", activityEventCount)
	}

	wm.Close()
}

// TestWindowMonitorActivityEventFormat verifies that activity events have the correct session ID format
func TestWindowMonitorActivityEventFormat(t *testing.T) {
	socketPath := createTestSocket(t)
	defer killTmuxServer(socketPath)

	logger := tap.NewDiscardLogger()

	// Create sessions
	createTmuxSession(t, socketPath, "test-monitor")
	createTmuxSession(t, socketPath, "sprite-exec-123")

	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	wm := NewWindowMonitor(ctx, "test-monitor").
		WithSocketPath(socketPath).
		WithConfigPath("").
		WithCommand(exec.Command("tmux"))

	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	if err := wm.Start(ctx); err != nil {
		t.Fatalf("Failed to start window monitor: %v", err)
	}

	// Wait briefly for initial discovery and require an immediate activity (or active) event on link
	requiredEventDeadline := time.Now().Add(2 * time.Second)
	gotInitialActivity := false
	for time.Now().Before(requiredEventDeadline) {
		select {
		case e := <-wm.GetEventChannel():
			if e.EventType == "activity" || e.EventType == "active" {
				gotInitialActivity = true
			}
		default:
		}
		if gotInitialActivity {
			break
		}
		time.Sleep(25 * time.Millisecond)
	}
	if !gotInitialActivity {
		t.Fatalf("expected immediate 'activity' or 'active' event upon linking, but none received within 2s")
	}

	// Send output
	sendKeysToPane(t, socketPath, "sprite-exec-123", "echo 'format test'")
	sendKeysToPane(t, socketPath, "sprite-exec-123", "Enter")

	// Collect events
	timeout := time.After(3 * time.Second)
	eventTypes := make(map[string][]string) // eventType -> []sessionIDs

collectLoop:
	for {
		select {
		case event := <-wm.GetEventChannel():
			if event.OriginalSession != "" {
				eventTypes[event.EventType] = append(eventTypes[event.EventType], event.OriginalSession)
			}
		case <-timeout:
			break collectLoop
		}
	}

	// Verify all event types use consistent session ID format (with $ prefix)
	for eventType, sessions := range eventTypes {
		for _, sessionID := range sessions {
			if len(sessionID) == 0 {
				t.Errorf("Event type %q has empty session ID", eventType)
				continue
			}
			if sessionID[0] != '$' {
				t.Errorf("Event type %q has incorrect session ID format: %q (expected $-prefix)",
					eventType, sessionID)
			}
		}
		t.Logf("Event type %q: %d events with correct format", eventType, len(sessions))
	}

	wm.Close()
}

// TestWindowMonitorActiveInactiveTransitions verifies that active/inactive events fire correctly
func TestWindowMonitorActiveInactiveTransitions(t *testing.T) {
	socketPath := createTestSocket(t)
	defer killTmuxServer(socketPath)

	logger := tap.NewDiscardLogger()

	// Create sessions
	createTmuxSession(t, socketPath, "test-monitor")
	createTmuxSession(t, socketPath, "sprite-exec-777")

	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	wm := NewWindowMonitor(ctx, "test-monitor").
		WithSocketPath(socketPath).
		WithConfigPath("").
		WithCommand(exec.Command("tmux"))

	ctx, cancel := context.WithTimeout(context.Background(), 20*time.Second)
	defer cancel()

	if err := wm.Start(ctx); err != nil {
		t.Fatalf("Failed to start window monitor: %v", err)
	}

	// Wait for discovery
	time.Sleep(1 * time.Second)

	// Assert we have at least one linked window after discovery
	if len(wm.GetLinkedWindows()) == 0 {
		t.Fatalf("expected at least one linked window after discovery")
	}

	// Helper to collect events with a label
	collectEvents := func(label string, duration time.Duration) []WindowMonitorEvent {
		events := make([]WindowMonitorEvent, 0)
		timeout := time.After(duration)
		for {
			select {
			case event := <-wm.GetEventChannel():
				events = append(events, event)
				t.Logf("[%s] Event: type=%s, session=%s", label, event.EventType, event.OriginalSession)
			case <-timeout:
				return events
			}
		}
	}

	// Drain briefly, then trigger additional activity
	_ = collectEvents("drain-post-initial", 200*time.Millisecond)

	// Step 1: Send initial output to ensure session becomes active
	t.Log("Step 1: Sending initial output to activate session")
	sendKeysToPane(t, socketPath, "sprite-exec-777", "echo 'initial'")
	sendKeysToPane(t, socketPath, "sprite-exec-777", "Enter")

	// Collect events - should include activity with data for the echo; 'active' may or may not appear
	step1Events := collectEvents("step1", 2*time.Second)
	activityWithData := false
	for _, event := range step1Events {
		if event.EventType == "activity" && len(event.Data) > 0 {
			activityWithData = true
			break
		}
	}
	if !activityWithData {
		t.Fatalf("expected an 'activity' event with data after sending initial output")
	}

	// Step 2: Wait >5 seconds (inactivity timeout) → should get "inactive" event
	t.Log("Step 2: Waiting for inactivity timeout (6 seconds)")
	events := collectEvents("step2-wait", 6500*time.Millisecond)

	inactiveFound := false
	for _, event := range events {
		if event.EventType == "inactive" {
			inactiveFound = true
			t.Logf("✓ Found 'inactive' event for session %s", event.OriginalSession)
			break
		}
	}
	if !inactiveFound {
		t.Error("Expected 'inactive' event after timeout, but didn't receive one")
		t.Logf("Events during wait: %d", len(events))
	}
	// Stats should show all sessions inactive now
	{
		stats := wm.GetActivityStats()
		for id, s := range stats {
			if s.IsActive {
				t.Errorf("expected session %s to be inactive in stats after timeout", id)
			}
		}
	}

	// Step 3: Send more output → should get "active" event again (reactivation)
	t.Log("Step 3: Sending output to reactivate")
	sendKeysToPane(t, socketPath, "sprite-exec-777", "echo 'reactivation'")
	sendKeysToPane(t, socketPath, "sprite-exec-777", "Enter")

	events = collectEvents("step3", 2*time.Second)

	activeAgainFound := false
	for _, event := range events {
		if event.EventType == "active" {
			activeAgainFound = true
			t.Logf("✓ Found 'active' event for reactivation, session %s", event.OriginalSession)
			break
		}
	}
	if !activeAgainFound {
		t.Error("Expected 'active' event after reactivation, but didn't receive one")
	}
	// Stats should reflect reactivation for at least one session
	{
		stats := wm.GetActivityStats()
		anyActive := false
		for _, s := range stats {
			if s.IsActive {
				anyActive = true
				break
			}
		}
		if !anyActive {
			t.Errorf("expected stats to show at least one active session after reactivation")
		}
	}

	// Verify session IDs have correct format in active/inactive events
	for _, event := range events {
		if (event.EventType == "active" || event.EventType == "inactive") && len(event.OriginalSession) > 0 {
			if event.OriginalSession[0] != '$' {
				t.Errorf("Event type %q has incorrect session ID format: %q (expected $-prefix)",
					event.EventType, event.OriginalSession)
			}
		}
	}

	wm.Close()
}
