package tmux

import (
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"testing"
	"time"

	"github.com/superfly/sprite-env/pkg/tap"
)

// Simulates the /exec detachable path using tmux.Manager and verifies that
// the window monitor observes activity without requiring artificial waits.
func TestMonitorSeesDetachableExecOutput(t *testing.T) {
	socketPath := createTestSocket(t)
	defer killTmuxServer(socketPath)

	// Provide a minimal tmux config file path for Manager (it always passes -f)
	tmpDir := t.TempDir()
	cfgPath := filepath.Join(tmpDir, "tmux.conf")
	if err := os.WriteFile(cfgPath, []byte(""), 0644); err != nil {
		t.Fatalf("failed to write temp tmux config: %v", err)
	}

	logger := tap.NewDiscardLogger()
	ctx := tap.WithLogger(context.Background(), logger)

	m := NewManager(ctx, Options{
		TmuxBinary: "tmux",
		SocketPath: socketPath,
		ConfigPath: cfgPath,
	})

	// Pre-create an exec session outside the manager (simulate an existing session)
	testID := "9001"
	execSessionName := "sprite-exec-" + testID
	createTmuxSession(t, socketPath, execSessionName)
	t.Cleanup(func() {
		_ = exec.Command("tmux", "-S", socketPath, "kill-session", "-t", execSessionName).Run()
	})

	// Send initial output immediately (do not wait for monitor)
	sendKeysToPane(t, socketPath, execSessionName, "echo FIRST_MONITOR_OK")
	sendKeysToPane(t, socketPath, execSessionName, "Enter")

	// Trigger manager to start the window monitor lazily without creating another session
	// (NewSession enqueues monitor start)
	dummyBase := exec.Command("true")
	_, _ /*unused*/, _ = m.NewSession(dummyBase, false)

	// Now wait until the window monitor event channel is available (lazy-started by manager)
	var evCh <-chan WindowMonitorEvent
	deadline := time.Now().Add(3 * time.Second)
	for time.Now().Before(deadline) {
		evCh = m.GetWindowMonitorEvents()
		if evCh != nil {
			break
		}
		time.Sleep(25 * time.Millisecond)
	}
	if evCh == nil {
		t.Fatal("window monitor did not start (event channel nil)")
	}

	// Send more output after we have started monitoring events
	sendKeysToPane(t, socketPath, execSessionName, "echo SECOND_MONITOR_OK")
	sendKeysToPane(t, socketPath, execSessionName, "Enter")

	// Collect events: expect an 'active' (from linking/initial activity) and at least one 'activity' with data (from second output)
	gotActive := false
	gotActivityWithData := false
	waitUntil := time.Now().Add(3 * time.Second)
	for time.Now().Before(waitUntil) {
		select {
		case ev := <-evCh:
			if ev.EventType == "active" {
				gotActive = true
			}
			if ev.EventType == "activity" && len(ev.Data) > 0 {
				gotActivityWithData = true
			}
		default:
		}
		if gotActive && gotActivityWithData {
			break
		}
		time.Sleep(25 * time.Millisecond)
	}
	if !gotActive || !gotActivityWithData {
		t.Fatalf("expected active and activity-with-data events, got active=%v activityWithData=%v", gotActive, gotActivityWithData)
	}

	// Done
}
