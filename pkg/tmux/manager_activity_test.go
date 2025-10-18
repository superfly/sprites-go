package tmux

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"testing"
	"time"
)

// Active status/edge-case parity with terminal tests using WindowMonitor
func TestManager_Activity_ActiveStatusAndEdge(t *testing.T) {
	if testing.Short() {
		t.Skip("short mode")
	}

	socketPath := fmt.Sprintf("/tmp/tmux-activity-test-%d-%d", os.Getpid(), time.Now().UnixNano())
	t.Cleanup(func() {
		os.Remove(socketPath)
		exec.Command("tmux", "-S", socketPath, "kill-server").Run()
	})

	ctx := context.Background()
	wm := NewWindowMonitor(ctx, "activity-monitor").
		WithSocketPath(socketPath).
		WithConfigPath("").
		WithCommand(exec.Command("tmux"))
	if err := wm.Start(ctx); err != nil {
		t.Fatalf("start window monitor: %v", err)
	}
	defer wm.Close()

	// Allow initialization
	time.Sleep(100 * time.Millisecond)

	// Create test sessions
	exec.Command("tmux", "-S", socketPath, "new-session", "-d", "-s", "sprites-exec-1").Run()
	exec.Command("tmux", "-S", socketPath, "new-session", "-d", "-s", "sprites-exec-2").Run()

	time.Sleep(500 * time.Millisecond)

	// Edge case: no manager monitor
	m := NewManager(ctx, Options{SocketPath: socketPath, TmuxBinary: "tmux", SessionPrefix: "sprites"})
	// wire monitor to manager (test-only)
	m.windowMonitor = wm
	info := m.GetAllSessionActivityInfo()
	_ = info
}
