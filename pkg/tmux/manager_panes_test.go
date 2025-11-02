package tmux

import (
	"context"
	"fmt"
	"os/exec"
	"testing"
	"time"
)

// Parity for GetSessionPanePIDs edge/integration behaviors
func TestManager_GetSessionPanePIDs_EdgeCases(t *testing.T) {
	m := NewManager(context.Background(), Options{})
	if _, err := m.GetSessionPanePIDs(""); err == nil {
		t.Fatalf("expected error for empty session id")
	}
}

func TestManager_GetSessionPanePIDs_Integration(t *testing.T) {
	if _, err := exec.LookPath("tmux"); err != nil {
		t.Skip("tmux not found")
	}
	socketPath := createTestSocket(t)
	defer killTmuxServer(socketPath)

	ctx := context.Background()
	m := NewManager(ctx, Options{SocketPath: socketPath, TmuxBinary: "tmux", ConfigPath: ""})

	sessionID := "test-pane-0"
	sessionName := fmt.Sprintf("sprite-exec-%s", sessionID)
	cmd := exec.Command("tmux", "-S", socketPath,
		"new-session", "-d", "-s", sessionName, "/bin/sh", "-c", "sleep 300")
	if err := cmd.Run(); err != nil {
		t.Fatalf("create tmux session: %v", err)
	}
	defer m.KillSession(sessionID)

	time.Sleep(200 * time.Millisecond)
	if !m.SessionExists(sessionID) {
		t.Fatalf("session not found after creation")
	}

	pids, err := m.GetSessionPanePIDs(sessionID)
	if err != nil {
		t.Fatalf("GetSessionPanePIDs error: %v", err)
	}
	if len(pids) != 1 {
		t.Fatalf("expected 1 pid, got %d", len(pids))
	}
}
