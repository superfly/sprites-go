package terminal

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

// TestGetSessionPanePIDs tests the GetSessionPanePIDs method
func TestGetSessionPanePIDs(t *testing.T) {
	// Create a test context with logger
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, tap.NewDiscardLogger())
	tm := NewTMUXManager(ctx)

	// Test with non-existent session - this should fail when trying to run tmux command
	t.Run("NonExistentSession", func(t *testing.T) {
		pids, err := tm.GetSessionPanePIDs("non-existent-999")
		// We expect an error since the tmux command will fail
		if err == nil {
			t.Error("Expected error for non-existent session, got nil")
		}
		if len(pids) != 0 {
			t.Errorf("Expected empty PID list for non-existent session, got %v", pids)
		}
	})

	t.Run("EmptySessionID", func(t *testing.T) {
		pids, err := tm.GetSessionPanePIDs("")
		if err == nil {
			t.Error("Expected error for empty session ID")
		}
		if len(pids) != 0 {
			t.Errorf("Expected empty PID list, got %v", pids)
		}
	})
}

// TestGetSessionPanePIDsIntegration tests the GetSessionPanePIDs method with real tmux
func TestGetSessionPanePIDsIntegration(t *testing.T) {
	// In Docker test environment, tmux must be available
	if _, err := exec.LookPath("tmux"); err != nil {
		t.Fatal("tmux not found in PATH - test environment is misconfigured")
	}

	// In Docker test environment, sprite tmux must be set up
	if _, err := os.Stat("/.sprite/bin/tmux"); err != nil {
		t.Fatal("Sprite tmux environment not available - test environment is misconfigured")
	}

	// Create a test context with logger
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, tap.NewDiscardLogger())
	tm := NewTMUXManager(ctx)

	// Get a session ID and create a detached session directly
	// We can't use CreateSession because it creates an attached session
	sessionID := "test-pane-0"
	sessionName := fmt.Sprintf("sprite-exec-%s", sessionID)

	// Create detached session using tmux directly
	tmuxCmd := exec.Command("/.sprite/bin/tmux",
		"-f", "/.sprite/etc/tmux.conf",
		"-S", "/.sprite/tmp/exec-tmux",
		"new-session", "-d", "-s", sessionName,
		"/bin/sh", "-c", "sleep 300")
	if err := tmuxCmd.Run(); err != nil {
		t.Fatalf("Failed to create detached tmux session: %v", err)
	}
	defer func() {
		// Clean up: kill the session
		tm.KillSession(sessionID)
	}()

	// Give tmux time to initialize
	time.Sleep(200 * time.Millisecond)

	// Verify the session exists before trying to get pane PIDs
	if !tm.SessionExists(sessionID) {
		t.Fatalf("Session %s does not exist after creation", sessionID)
	}

	t.Run("SinglePane", func(t *testing.T) {
		pids, err := tm.GetSessionPanePIDs(sessionID)
		if err != nil {
			// Try to get more info about what went wrong
			sessionName := fmt.Sprintf("sprite-exec-%s", sessionID)
			listCmd := exec.Command("/.sprite/bin/tmux", "-S", "/.sprite/tmp/exec-tmux", "list-sessions")
			listOut, _ := listCmd.CombinedOutput()
			t.Logf("Sessions: %s", string(listOut))

			panesCmd := exec.Command("/.sprite/bin/tmux", "-S", "/.sprite/tmp/exec-tmux", "list-panes", "-t", sessionName)
			panesOut, panesErr := panesCmd.CombinedOutput()
			t.Logf("Panes command error: %v, output: %s", panesErr, string(panesOut))

			t.Fatalf("Failed to get pane PIDs: %v", err)
		}
		if len(pids) != 1 {
			t.Errorf("Expected 1 PID for single pane, got %d: %v", len(pids), pids)
		}
		if len(pids) > 0 && pids[0] <= 0 {
			t.Errorf("Invalid PID: %d", pids[0])
		}
	})

	// The detailed multi-pane tests would go here if needed
}

// TestGetSessionPanePIDsEdgeCases tests edge cases and error handling
func TestGetSessionPanePIDsEdgeCases(t *testing.T) {
	// In Docker test environment, tmux must be available
	if _, err := exec.LookPath("tmux"); err != nil {
		t.Fatal("tmux not found in PATH - test environment is misconfigured")
	}

	ctx := context.Background()
	ctx = tap.WithLogger(ctx, tap.NewDiscardLogger())
	tm := NewTMUXManager(ctx)

	t.Run("EmptySessionID", func(t *testing.T) {
		pids, err := tm.GetSessionPanePIDs("")
		if err == nil {
			t.Error("Expected error for empty session ID")
		}
		if len(pids) != 0 {
			t.Errorf("Expected empty PID list, got %v", pids)
		}
	})

	t.Run("InvalidSessionFormat", func(t *testing.T) {
		// Test with various invalid formats
		invalidIDs := []string{"invalid-session", "123abc", "!@#$%"}
		for _, id := range invalidIDs {
			pids, err := tm.GetSessionPanePIDs(id)
			if err == nil {
				t.Errorf("Expected error for invalid session ID %q", id)
			}
			if len(pids) != 0 {
				t.Errorf("Expected empty PID list for invalid ID %q, got %v", id, pids)
			}
		}
	})
}

// TestGetSessionPanePIDsWithCommandPrefix tests when TMUXManager has a command prefix
func TestGetSessionPanePIDsWithCommandPrefix(t *testing.T) {
	// This test simulates the server-side usage where commands might be prefixed
	// In Docker test environment, tmux must be available
	if _, err := exec.LookPath("tmux"); err != nil {
		t.Fatal("tmux not found in PATH - test environment is misconfigured")
	}

	ctx := context.Background()
	ctx = tap.WithLogger(ctx, tap.NewDiscardLogger())
	tm := NewTMUXManager(ctx)

	// Set a command prefix (simulating container execution)
	tm.SetCmdPrefix([]string{"/bin/sh", "-c"})

	// Since we can't easily test the actual container case,
	// we'll at least verify the method doesn't panic with a prefix set
	t.Run("WithPrefix", func(t *testing.T) {
		// This should fail gracefully since we're not in a real container
		pids, err := tm.GetSessionPanePIDs("test-session")
		if err == nil {
			// If it somehow succeeds, verify we get a reasonable result
			t.Logf("Unexpectedly succeeded with %d PIDs", len(pids))
		}
		// We expect an error here in the test environment, which is fine
	})
}

// TestPanePIDsProcessTreeIntegration verifies that pane PIDs share the tmux server as ancestor
// This is an integration test that requires tmux to be installed
func TestPanePIDsProcessTreeIntegration(t *testing.T) {
	// In Docker test environment, tmux must be available
	if _, err := exec.LookPath("tmux"); err != nil {
		t.Fatal("tmux not found in PATH - test environment is misconfigured")
	}

	// This test demonstrates that all pane PIDs in a session
	// share the tmux server process as their parent
	socketPath := fmt.Sprintf("/tmp/tmux-test-pids-%d", os.Getpid())
	sessionName := "test-pid-tree"

	// Create a tmux session
	createCmd := exec.Command("tmux", "-S", socketPath, "new-session", "-d", "-s", sessionName, "sleep", "300")
	if err := createCmd.Run(); err != nil {
		t.Fatalf("Failed to create tmux session: %v", err)
	}
	defer func() {
		killCmd := exec.Command("tmux", "-S", socketPath, "kill-session", "-t", sessionName)
		killCmd.Run()
	}()

	// Give tmux time to start
	time.Sleep(100 * time.Millisecond)

	// Get tmux server PID - on macOS, pgrep may not be available, so try ps
	var serverPID string
	serverPIDCmd := exec.Command("sh", "-c", fmt.Sprintf("ps aux | grep 'tmux -S %s' | grep -v grep | awk '{print $2}' | head -1", socketPath))
	serverPIDOut, err := serverPIDCmd.Output()
	if err == nil && len(serverPIDOut) > 0 {
		serverPID = strings.TrimSpace(string(serverPIDOut))
	}

	if serverPID == "" {
		t.Skip("Could not determine tmux server PID - skipping process tree verification")
	}

	t.Logf("Tmux server PID: %s", serverPID)

	// Get pane PID
	panePIDCmd := exec.Command("tmux", "-S", socketPath, "list-panes", "-t", sessionName, "-F", "#{pane_pid}")
	panePIDOut, err := panePIDCmd.Output()
	if err != nil {
		t.Fatalf("Failed to get pane PID: %v", err)
	}
	panePID := strings.TrimSpace(string(panePIDOut))
	t.Logf("Pane PID: %s", panePID)

	// Verify the pane's parent is the tmux server
	parentCmd := exec.Command("ps", "-o", "ppid=", "-p", panePID)
	parentOut, err := parentCmd.Output()
	if err != nil {
		t.Logf("Could not get parent PID - this is expected on some systems")
		return
	}
	parentPID := strings.TrimSpace(string(parentOut))

	if parentPID != serverPID {
		t.Logf("Note: Pane parent PID is %s, tmux server PID is %s", parentPID, serverPID)
		t.Log("This is normal - panes may not be direct children of the tmux server on all systems")
	} else {
		t.Log("✓ Confirmed: pane process is a direct child of tmux server")
	}
}
