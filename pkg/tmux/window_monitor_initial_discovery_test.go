package tmux

import (
	"context"
	"os/exec"
	"testing"
	"time"

	"github.com/superfly/sprite-env/pkg/tap"
)

// Verifies the initial discovery goroutine runs, logs, links an existing sprite-exec window, and emits a new event
func TestInitialDiscoveryLinksExistingExecWindow(t *testing.T) {
	socketPath := createTestSocket(t)
	defer killTmuxServer(socketPath)

	// Pre-create monitor session and a sprite-exec session before starting the monitor
	createTmuxSession(t, socketPath, "test-monitor")
	createTmuxSession(t, socketPath, "sprite-exec-123")

	// Use discard logger that still feeds the global buffer
	logger := tap.NewDiscardLogger()

	ctx := tap.WithLogger(context.Background(), logger)
	wm := NewWindowMonitor(ctx, "test-monitor").
		WithSocketPath(socketPath).
		WithConfigPath("").
		WithCommand(exec.Command("tmux"))

	runCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	if err := wm.Start(runCtx); err != nil {
		t.Fatalf("Failed to start window monitor: %v", err)
	}

	// Expect 'activity' and 'new' events from linking (activity should fire on link)
	gotNew := false
	gotActivity := false
	waitEventsDeadline := time.Now().Add(3 * time.Second)
	for time.Now().Before(waitEventsDeadline) {
		select {
		case ev := <-wm.GetEventChannel():
			if ev.EventType == "new" {
				gotNew = true
			}
			if ev.EventType == "activity" {
				gotActivity = true
			}
		default:
		}
		if gotNew && gotActivity {
			break
		}
		time.Sleep(25 * time.Millisecond)
	}
	if !gotNew || !gotActivity {
		t.Errorf("Expected 'new' and 'activity' events on linking, got new=%v activity=%v", gotNew, gotActivity)
	}

	// Also verify at least one window is linked
	if len(wm.GetLinkedWindows()) == 0 {
		t.Error("Expected at least one linked window after initial discovery")
	}

	_ = wm.Close()
}

// Verifies that discovery marks a newly linked session as active without requiring output,
// and that it transitions to inactive after the timeout
func TestInitialDiscoveryMarksActiveWithoutOutput(t *testing.T) {
	socketPath := createTestSocket(t)
	defer killTmuxServer(socketPath)

	// Pre-create monitor and exec session
	createTmuxSession(t, socketPath, "test-monitor")
	createTmuxSession(t, socketPath, "sprite-exec-555")

	logger := tap.NewDiscardLogger()
	ctx := tap.WithLogger(context.Background(), logger)
	wm := NewWindowMonitor(ctx, "test-monitor").
		WithSocketPath(socketPath).
		WithConfigPath("").
		WithCommand(exec.Command("tmux"))

	runCtx, cancel := context.WithTimeout(context.Background(), 15*time.Second)
	defer cancel()

	if err := wm.Start(runCtx); err != nil {
		t.Fatalf("Failed to start window monitor: %v", err)
	}

	// Wait for stats to include at least one session marked active
	activeSeen := false
	deadline := time.Now().Add(2 * time.Second)
	for time.Now().Before(deadline) {
		stats := wm.GetActivityStats()
		for _, s := range stats {
			if s.IsActive {
				activeSeen = true
				break
			}
		}
		if activeSeen {
			break
		}
		time.Sleep(50 * time.Millisecond)
	}
	if !activeSeen {
		t.Fatal("Expected newly linked session to be marked active")
	}

	// After inactivity timeout (>5s), expect an 'inactive' event
	inactiveSeen := false
	waitUntil := time.Now().Add(7 * time.Second)
	for time.Now().Before(waitUntil) {
		select {
		case ev := <-wm.GetEventChannel():
			if ev.EventType == "inactive" {
				inactiveSeen = true
			}
		default:
		}
		if inactiveSeen {
			break
		}
		time.Sleep(100 * time.Millisecond)
	}
	if !inactiveSeen {
		t.Error("Expected an 'inactive' event after inactivity timeout")
	}

	_ = wm.Close()
}
