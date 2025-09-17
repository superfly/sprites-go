package terminal

import (
	"context"
	"log/slog"
	"strconv"
	"strings"
	"testing"

	"github.com/superfly/sprite-env/pkg/tap"
)

func TestTMUXManager_CreateSession(t *testing.T) {
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, slog.Default())
	tm := NewTMUXManager(ctx)

	// Test creating a new session
	sessionID, cmd, args := tm.CreateSession("echo", []string{"hello"}, false)

	// Check session ID is numeric
	if sessionID == "" {
		t.Error("Expected non-empty session ID")
	}
	if _, err := strconv.Atoi(sessionID); err != nil {
		t.Errorf("Expected numeric session ID, got %s", sessionID)
	}

	if cmd != "/.sprite/bin/tmux" {
		t.Errorf("Expected command to be /.sprite/bin/tmux, got %s", cmd)
	}

	// Check that args contain config, socket and new-session command
	// Expected: [-f /.sprite/etc/tmux.conf -S /.sprite/tmp/exec-tmux new-session -s sprite-exec-<id> cmd args...]
	if len(args) < 7 {
		t.Errorf("Expected at least 7 args, got %d: %v", len(args), args)
	}
	if args[0] != "-f" || args[1] != "/.sprite/etc/tmux.conf" {
		t.Errorf("Expected -f /.sprite/etc/tmux.conf, got %s %s", args[0], args[1])
	}
	if args[2] != "-S" || args[3] != "/.sprite/tmp/exec-tmux" {
		t.Errorf("Expected -S /.sprite/tmp/exec-tmux, got %s %s", args[2], args[3])
	}
	if args[4] != "new-session" || args[5] != "-s" {
		t.Errorf("Expected new-session -s, got %s %s", args[4], args[5])
	}
	if !strings.HasPrefix(args[6], "sprite-exec-") {
		t.Errorf("Expected session name to start with sprite-exec-, got %s", args[6])
	}
}

func TestTMUXManager_AttachSession(t *testing.T) {
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, slog.Default())
	tm := NewTMUXManager(ctx)

	// Test attaching to a session
	cmd, args := tm.AttachSession("3", false)

	if cmd != "/.sprite/bin/tmux" {
		t.Errorf("Expected command to be /.sprite/bin/tmux, got %s", cmd)
	}

	// Check that args contain config, socket and attach-session command
	// Expected: [-f /.sprite/etc/tmux.conf -S /.sprite/tmp/exec-tmux attach-session -t sprite-exec-3]
	if len(args) != 7 {
		t.Errorf("Expected 7 args, got %d: %v", len(args), args)
	}
	if args[0] != "-f" || args[1] != "/.sprite/etc/tmux.conf" {
		t.Errorf("Expected -f /.sprite/etc/tmux.conf, got %s %s", args[0], args[1])
	}
	if args[2] != "-S" || args[3] != "/.sprite/tmp/exec-tmux" {
		t.Errorf("Expected -S /.sprite/tmp/exec-tmux, got %s %s", args[2], args[3])
	}
	if args[4] != "attach-session" || args[5] != "-t" || args[6] != "sprite-exec-3" {
		t.Errorf("Expected attach-session -t sprite-exec-3, got %s %s %s", args[4], args[5], args[6])
	}
}

func TestTMUXManager_SessionExists(t *testing.T) {
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, slog.Default())
	tm := NewTMUXManager(ctx)

	// Test checking for a non-existent session
	// This will likely return false since we're not actually creating tmux sessions in tests
	exists := tm.SessionExists("99999")
	if exists {
		t.Log("Note: tmux session '99999' exists, which is unexpected in a test environment")
	}
}

func TestTMUXManager_ListSessions(t *testing.T) {
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, slog.Default())
	tm := NewTMUXManager(ctx)

	// This test just verifies the function doesn't panic
	sessions, err := tm.ListSessions()
	if err != nil {
		t.Logf("ListSessions returned error (expected if tmux not running): %v", err)
	}

	t.Logf("Found %d tmux sessions", len(sessions))
	for _, session := range sessions {
		t.Logf("  - %s", session)
	}
}

func TestTMUXManager_CreateSessionWithControlMode(t *testing.T) {
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, slog.Default())
	tm := NewTMUXManager(ctx)

	// Test creating a session with control mode
	sessionID, cmd, args := tm.CreateSession("bash", []string{}, true)

	// Check that -CC is in the args
	found := false
	for _, arg := range args {
		if arg == "-CC" {
			found = true
			break
		}
	}
	if !found {
		t.Error("Expected -CC flag in args for control mode")
	}

	// Check session ID is numeric
	if sessionID == "" {
		t.Error("Expected non-empty session ID")
	}

	if cmd != "/.sprite/bin/tmux" {
		t.Errorf("Expected command to be /.sprite/bin/tmux, got %s", cmd)
	}
}

func TestTMUXManager_AttachSessionWithControlMode(t *testing.T) {
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, slog.Default())
	tm := NewTMUXManager(ctx)

	// Test attaching with control mode
	cmd, args := tm.AttachSession("5", true)

	if cmd != "/.sprite/bin/tmux" {
		t.Errorf("Expected command to be /.sprite/bin/tmux, got %s", cmd)
	}

	// Check that -CC is in the args
	found := false
	for _, arg := range args {
		if arg == "-CC" {
			found = true
			break
		}
	}
	if !found {
		t.Error("Expected -CC flag in args for control mode")
	}
}
