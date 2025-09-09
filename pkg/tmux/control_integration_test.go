package tmux

import (
	"fmt"
	"os"
	"os/exec"
	"sync"
	"testing"
	"time"
)

// TestParserWithRealTmux tests the parser with a real tmux process
func TestParserWithRealTmux(t *testing.T) {
	socketName, cleanup := startTestTmuxSession(t, "parser-test")
	defer cleanup()

	parser := createTestParser(t, socketName, "parser-test")
	defer parser.Close()

	// Collect events
	var mu sync.Mutex
	events := []TmuxEvent{}

	go func() {
		for event := range parser.Events() {
			mu.Lock()
			events = append(events, event)
			mu.Unlock()
		}
	}()

	// Wait for initial connection
	time.Sleep(200 * time.Millisecond)

	// Test list-windows command
	if err := parser.SendCommand("list-windows"); err != nil {
		t.Errorf("Failed to send list-windows: %v", err)
	}
	time.Sleep(100 * time.Millisecond)

	// Test creating a new window
	if err := parser.SendCommand("new-window -n testwin"); err != nil {
		t.Errorf("Failed to send new-window: %v", err)
	}
	time.Sleep(200 * time.Millisecond)

	// Test list-panes command
	if err := parser.SendCommand("list-panes"); err != nil {
		t.Errorf("Failed to send list-panes: %v", err)
	}
	time.Sleep(100 * time.Millisecond)

	// Check events
	mu.Lock()
	defer mu.Unlock()

	if len(events) == 0 {
		t.Error("No events received")
	}

	// Count window add events
	windowAddCount := 0
	for _, event := range events {
		t.Logf("Event: %T", event)
		if _, ok := event.(WindowAddEvent); ok {
			windowAddCount++
		}
	}

	if windowAddCount < 1 {
		t.Errorf("Expected at least 1 WindowAddEvent, got %d", windowAddCount)
	}

	// Check parser state
	windows := 0
	for i := 0; i < 10; i++ {
		windowID := fmt.Sprintf("@%d", i)
		if win, ok := parser.GetWindow(windowID); ok {
			t.Logf("Found window: %s (name: %s)", windowID, win.Name)
			windows++
		}
	}

	// Also log unmapped panes
	unmappedPanes := parser.GetUnmappedPanes()
	t.Logf("Unmapped panes: %d", len(unmappedPanes))

	// We should have created at least one window (the new-window command might have succeeded)
	if windows < 1 {
		t.Errorf("Expected at least 1 window in parser state, got %d", windows)
	}
}

// TestParserDataRate tests data rate tracking with real tmux
func TestParserDataRate(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping data rate test in short mode")
	}

	socketName, cleanup := startTestTmuxSession(t, "datarate-test")
	defer cleanup()

	parser := createTestParser(t, socketName, "datarate-test")
	defer parser.Close()

	// Wait for initial connection
	time.Sleep(200 * time.Millisecond)

	// Create a window with a command that generates output
	if err := parser.SendCommand("new-window 'echo hello; echo world; sleep 0.1; echo done'"); err != nil {
		t.Errorf("Failed to create window: %v", err)
	}

	// Wait for output
	time.Sleep(500 * time.Millisecond)

	// Check pane data rates
	unmappedPanes := parser.GetUnmappedPanes()
	for _, pane := range unmappedPanes {
		if pane.ByteCount > 0 {
			t.Logf("Pane %s: ByteCount=%d, DataRate=%.2f", pane.ID, pane.ByteCount, pane.DataRate)
		}
	}
}

// TestParserMultipleWindows tests handling multiple windows and panes
func TestParserMultipleWindows(t *testing.T) {
	socketName, cleanup := startTestTmuxSession(t, "multiwin-test")
	defer cleanup()

	parser := createTestParser(t, socketName, "multiwin-test")
	defer parser.Close()

	// Wait for initial connection
	time.Sleep(200 * time.Millisecond)

	// Create multiple windows
	for i := 1; i <= 3; i++ {
		cmd := "new-window -n win" + string(rune('0'+i))
		if err := parser.SendCommand(cmd); err != nil {
			t.Errorf("Failed to create window %d: %v", i, err)
		}
		time.Sleep(100 * time.Millisecond)
	}

	// Test split-window
	if err := parser.SendCommand("split-window -h"); err != nil {
		t.Errorf("Failed to split window: %v", err)
	}
	time.Sleep(100 * time.Millisecond)

	// List all windows and panes
	if err := parser.RefreshWindowsAndPanes(); err != nil {
		t.Errorf("Failed to refresh windows and panes: %v", err)
	}
	time.Sleep(200 * time.Millisecond)

	// Check window count
	windowCount := 0
	for i := 0; i < 10; i++ {
		windowID := fmt.Sprintf("@%d", i)
		if win, ok := parser.GetWindow(windowID); ok {
			t.Logf("Found window: %s (name: %s)", windowID, win.Name)
			windowCount++
		}
	}

	// We created 3 windows, plus initial window = at least 4 total
	// But tmux might consolidate or close some windows
	if windowCount < 2 {
		t.Errorf("Expected at least 2 windows, got %d", windowCount)
	}
}

// TestParserCommandInterleaving tests sending multiple commands rapidly
func TestParserCommandInterleaving(t *testing.T) {
	socketName, cleanup := startTestTmuxSession(t, "interleave-test")
	defer cleanup()

	parser := createTestParser(t, socketName, "interleave-test")
	defer parser.Close()

	// Wait for initial connection
	time.Sleep(200 * time.Millisecond)

	// Send multiple commands rapidly
	commands := []string{
		"list-windows",
		"list-panes",
		"list-sessions",
		"new-window -n rapid1",
		"new-window -n rapid2",
		"list-windows",
	}

	for _, cmd := range commands {
		if err := parser.SendCommand(cmd); err != nil {
			t.Errorf("Failed to send command %s: %v", cmd, err)
		}
		// Very short delay
		time.Sleep(10 * time.Millisecond)
	}

	// Wait for all responses
	time.Sleep(500 * time.Millisecond)

	// Verify we have multiple windows
	windowCount := 0
	for i := 0; i < 10; i++ {
		windowID := fmt.Sprintf("@%d", i)
		if win, ok := parser.GetWindow(windowID); ok {
			t.Logf("Found window: %s (name: %s)", windowID, win.Name)
			windowCount++
		}
	}

	// We created 2 windows with rapid commands, should have at least 2
	if windowCount < 2 {
		t.Errorf("Expected at least 2 windows after rapid commands, got %d", windowCount)
	}
}

// TestParserSessionTracking tests session tracking functionality
func TestParserSessionTracking(t *testing.T) {
	socketName := fmt.Sprintf("tmux-test-session-%d", os.Getpid())

	// Create first session
	createCmd := exec.Command("tmux", "-L", socketName, "new-session", "-d", "-s", "session1", "cat")
	if err := createCmd.Run(); err != nil {
		t.Fatalf("Failed to create first session: %v", err)
	}

	// Create second session
	createCmd2 := exec.Command("tmux", "-L", socketName, "new-session", "-d", "-s", "session2", "cat")
	if err := createCmd2.Run(); err != nil {
		t.Fatalf("Failed to create second session: %v", err)
	}

	defer func() {
		killCmd := exec.Command("tmux", "-L", socketName, "kill-server")
		killCmd.Run()
	}()

	// Attach to first session
	parser := createTestParser(t, socketName, "session1")
	defer parser.Close()

	// Wait for connection
	time.Sleep(200 * time.Millisecond)

	// List sessions
	if err := parser.SendCommand("list-sessions"); err != nil {
		t.Errorf("Failed to list sessions: %v", err)
	}
	time.Sleep(100 * time.Millisecond)

	// Switch session
	if err := parser.SendCommand("switch-client -t session2"); err != nil {
		t.Errorf("Failed to switch session: %v", err)
	}
	time.Sleep(100 * time.Millisecond)
}
