package tmux

import (
    "context"
    "fmt"
    "os"
    "os/exec"
    "strings"
    "testing"
    "time"

    "github.com/superfly/sprite-env/pkg/tap"
)

// Helper to create a test tmux socket
func createTestSocket(t *testing.T) string {
	// Use /tmp directly to avoid long path issues with t.TempDir()
	socketPath := fmt.Sprintf("/tmp/tmux-test-%d-%d", os.Getpid(), time.Now().UnixNano())
	// Register cleanup
	t.Cleanup(func() {
		os.Remove(socketPath)
	})
	return socketPath
}

// Helper to kill tmux server
func killTmuxServer(socketPath string) {
    ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
    defer cancel()
    _ = exec.CommandContext(ctx, "tmux", "-S", socketPath, "kill-server").Run()
}

// Helper to create a tmux session
func createTmuxSession(t *testing.T, socketPath, sessionName string) {
    t.Helper()
    // First try to kill any existing session with this name (short timeout)
    ctxKill, cancelKill := context.WithTimeout(context.Background(), 1*time.Second)
    _ = exec.CommandContext(ctxKill, "tmux", "-S", socketPath, "kill-session", "-t", sessionName).Run()
    cancelKill()

    // Create a detached session and return immediately (short timeout)
    ctxCreate, cancelCreate := context.WithTimeout(context.Background(), 3*time.Second)
    defer cancelCreate()
    cmd := exec.CommandContext(ctxCreate, "tmux", "-S", socketPath, "new-session", "-d", "-s", sessionName)
    if err := cmd.Run(); err != nil {
        t.Fatalf("Failed to create session %s: %v", sessionName, err)
    }
}

// Helper to send keys to a tmux pane
func sendKeysToPane(t *testing.T, socketPath, target, keys string) {
    t.Helper()
    ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
    defer cancel()
    if err := exec.CommandContext(ctx, "tmux", "-S", socketPath, "send-keys", "-t", target, keys).Run(); err != nil {
        t.Fatalf("Failed to send keys to %s: %v", target, err)
    }
}

// Helper to create a window in a session
func createWindow(t *testing.T, socketPath, sessionName, windowName string) string {
    t.Helper()
    ctx, cancel := context.WithTimeout(context.Background(), 3*time.Second)
    defer cancel()
    cmd := exec.CommandContext(ctx, "tmux", "-S", socketPath, "new-window", "-t", sessionName, "-n", windowName, "-P", "-F", "#{window_id}")
    output, err := cmd.Output()
    if err != nil {
        t.Fatalf("Failed to create window: %v", err)
    }
    return strings.TrimSpace(string(output))
}

func TestWindowMonitorBasic(t *testing.T) {
	socketPath := createTestSocket(t)
	defer killTmuxServer(socketPath)

	// Don't override PATH - let the system find tmux naturally

	// Use discard logger to suppress output
	logger := tap.NewDiscardLogger()

	// Create monitor session
	createTmuxSession(t, socketPath, "test-monitor")

	// Create some sprite-exec sessions
	createTmuxSession(t, socketPath, "sprite-exec-1")
	createTmuxSession(t, socketPath, "sprite-exec-2")
	createTmuxSession(t, socketPath, "other-session") // Should be ignored

	// Create window monitor with test socket
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	wm := NewWindowMonitor(ctx, "test-monitor").
		WithSocketPath(socketPath).
		WithConfigPath(""). // No config file for tests
		WithCommand(exec.Command("tmux"))

	// Start the monitor with modified commands
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	// We need to override the command creation in the monitor
	// For this test, we'll create a modified version that accepts socket path
	cmd := exec.Command("tmux",
		"-S", socketPath,
		"-C",
		"attach-session", "-t", wm.monitorSession)

	parser, err := NewTmuxControlModeParser(cmd, nil)
	if err != nil {
		// Try creating the session
		cmd = exec.Command("tmux",
			"-S", socketPath,
			"-C",
			"new-session", "-s", wm.monitorSession, "-d")

		parser, err = NewTmuxControlModeParser(cmd, nil)
		if err != nil {
			t.Fatalf("Failed to start control mode: %v", err)
		}
	}
	wm.parser = parser

	// Start monitoring
	go wm.monitorLoop(ctx)

	// Trigger initial discovery by emitting SessionsChangedEvent
	select {
	case parser.events <- SessionsChangedEvent{}:
		t.Log("Sent SessionsChangedEvent to trigger discovery")
	case <-time.After(100 * time.Millisecond):
		t.Error("Failed to send SessionsChangedEvent")
	}

	// Wait for discovery to complete
	time.Sleep(1 * time.Second)

	// Verify windows were discovered and linked
	linkedWindows := wm.GetLinkedWindows()
	if len(linkedWindows) < 2 {
		t.Errorf("Expected at least 2 linked windows, got %d", len(linkedWindows))
	}

	// Send some output to sprite-exec-1
	sendKeysToPane(t, socketPath, "sprite-exec-1", "echo 'test output'")
	sendKeysToPane(t, socketPath, "sprite-exec-1", "Enter")

	// Collect events
	events := make([]WindowMonitorEvent, 0)
	timeout := time.After(3 * time.Second)

collectLoop:
	for {
		select {
		case event := <-wm.GetEventChannel():
			events = append(events, event)
			if event.EventType == "activity" && len(event.Data) > 0 {
				t.Logf("Got activity event: window=%s, session=%s, data=%q",
					event.WindowID, event.OriginalSession, string(event.Data))
			}
		case <-timeout:
			break collectLoop
		}
	}

	// Verify we got activity events
	activityFound := false
	for _, event := range events {
		if event.EventType == "activity" {
			activityFound = true
			break
		}
	}

	if !activityFound {
		t.Error("No activity events received")
	}

	// Clean up
	wm.Close()
}

func TestWindowMonitorMultipleSessions(t *testing.T) {
	socketPath := createTestSocket(t)
	defer killTmuxServer(socketPath)

	// Use discard logger to suppress output
	logger := tap.NewDiscardLogger()

	// Create multiple sprite-exec sessions (monitor will create its own session)
	sessions := []string{
		"sprite-exec-100",
		"sprite-exec-101",
		"sprite-exec-102",
	}

	for _, session := range sessions {
		createTmuxSession(t, socketPath, session)
	}

	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	wm := NewWindowMonitor(ctx, "test-monitor").
		WithSocketPath(socketPath).
		WithConfigPath(""). // No config file for tests
		WithCommand(exec.Command("tmux"))

	ctx, cancel := context.WithTimeout(context.Background(), 15*time.Second)
	defer cancel()

	// Start the monitor
	if err := wm.Start(ctx); err != nil {
		t.Fatalf("Failed to start window monitor: %v", err)
	}

	// Wait for discovery
	time.Sleep(1 * time.Second)

	// Check if windows were linked
	linkedWindows := wm.GetLinkedWindows()
	t.Logf("Linked windows after discovery: %d", len(linkedWindows))
	for windowID, sessionID := range linkedWindows {
		t.Logf("  Window %s -> Session %s", windowID, sessionID)
	}

	// Send output to each session
	for i, session := range sessions {
		msg := fmt.Sprintf("Message from %s", session)
		sendKeysToPane(t, socketPath, session, fmt.Sprintf("echo '%s'", msg))
		sendKeysToPane(t, socketPath, session, "Enter")
		time.Sleep(100 * time.Millisecond) // Small delay between sessions

		t.Logf("Sent message %d to %s", i, session)
	}

	// Collect events
	sessionActivity := make(map[string]int)
	timeout := time.After(5 * time.Second)

	for {
		select {
		case event := <-wm.GetEventChannel():
			if event.EventType == "activity" {
				// Count all activity events from any session
				sessionActivity[event.OriginalSession]++
			}
		case <-timeout:
			goto done
		}
	}

done:
	// Verify we got activity from multiple sessions
	if len(sessionActivity) < 2 {
		t.Errorf("Expected activity from at least 2 sessions, got %d", len(sessionActivity))
		for session, count := range sessionActivity {
			t.Logf("Session %s: %d events", session, count)
		}
	}

	wm.Close()
}

func TestWindowMonitorNewWindowDetection(t *testing.T) {
	socketPath := createTestSocket(t)
	defer killTmuxServer(socketPath)

	// Use discard logger to suppress output
	logger := tap.NewDiscardLogger()

	// Create monitor session
	createTmuxSession(t, socketPath, "test-monitor")

	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	wm := NewWindowMonitor(ctx, "test-monitor").
		WithSocketPath(socketPath).
		WithConfigPath(""). // No config file for tests
		WithCommand(exec.Command("tmux"))

	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	// Start monitor
	if err := wm.Start(ctx); err != nil {
		t.Fatalf("Failed to start window monitor: %v", err)
	}

	// Create a session after monitor started
	time.Sleep(1 * time.Second)
	createTmuxSession(t, socketPath, "sprite-exec-200")

	// Wait for discovery
	time.Sleep(2 * time.Second)

	// Check if new session was detected
	linkedWindows := wm.GetLinkedWindows()
	if len(linkedWindows) == 0 {
		t.Error("No windows were linked")
		t.Logf("Linked windows: %v", linkedWindows)
	}

	// Create another window in the existing session
	windowID := createWindow(t, socketPath, "sprite-exec-200", "new-window")
	t.Logf("Created new window: %s", windowID)

	// Manually trigger window discovery since new windows in other sessions don't generate events
	wm.discoverAndLinkWindows()

	// Wait for discovery to complete
	time.Sleep(500 * time.Millisecond)

	// The window count should have increased
	newLinkedWindows := wm.GetLinkedWindows()
	if len(newLinkedWindows) <= len(linkedWindows) {
		t.Error("New window was not detected")
		t.Logf("Windows before: %d, after: %d", len(linkedWindows), len(newLinkedWindows))
	}

	wm.Close()
}

func TestWindowMonitorWindowClose(t *testing.T) {
	socketPath := createTestSocket(t)
	defer killTmuxServer(socketPath)

	// Use discard logger to suppress output
	logger := tap.NewDiscardLogger()

	// Create sessions
	createTmuxSession(t, socketPath, "test-monitor")
	createTmuxSession(t, socketPath, "sprite-exec-300")

	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	wm := NewWindowMonitor(ctx, "test-monitor").
		WithSocketPath(socketPath).
		WithConfigPath(""). // No config file for tests
		WithCommand(exec.Command("tmux"))

	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	// Start the monitor
	if err := wm.Start(ctx); err != nil {
		t.Fatalf("Failed to start window monitor: %v", err)
	}

	// Wait for initial discovery
	time.Sleep(1 * time.Second)

	// Kill the sprite-exec session
	killCmd := exec.Command("tmux", "-S", socketPath, "kill-session", "-t", "sprite-exec-300")
	if err := killCmd.Run(); err != nil {
		t.Fatalf("Failed to kill session: %v", err)
	}

	// Wait for event
	timeout := time.After(3 * time.Second)
	closedEventReceived := false

	for {
		select {
		case event := <-wm.GetEventChannel():
			if event.EventType == "closed" {
				closedEventReceived = true
				t.Logf("Received closed event for window %s", event.WindowID)
			}
		case <-timeout:
			goto checkResult
		}
	}

checkResult:
	if !closedEventReceived {
		t.Error("Did not receive window closed event")
	}

	wm.Close()
}
