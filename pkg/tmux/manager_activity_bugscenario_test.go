package tmux

import (
    "context"
    "fmt"
    "os"
    "os/exec"
    "testing"
    "time"
)

// Ports the bug scenario test ensuring mapping/activity stay consistent for session 0
func TestManager_Activity_BugScenario_SessionZero(t *testing.T) {
    if testing.Short() {
        t.Skip("short mode")
    }
    if _, err := exec.LookPath("tmux"); err != nil {
        t.Skip("tmux not found")
    }

    socketPath := fmt.Sprintf("/tmp/tmux-bug-%d", os.Getpid())
    t.Cleanup(func() {
        os.Remove(socketPath)
        exec.Command("tmux", "-S", socketPath, "kill-server").Run()
    })

    ctx := context.Background()
    monitorSession := "bug-monitor"
    _ = exec.Command("tmux", "-S", socketPath, "new-session", "-d", "-s", monitorSession).Run()

    wm := NewWindowMonitor(ctx, monitorSession).
        WithSocketPath(socketPath).
        WithConfigPath("").
        WithCommand(exec.Command("tmux"))
    if err := wm.Start(ctx); err != nil {
        t.Fatalf("start window monitor: %v", err)
    }
    defer wm.Close()

    time.Sleep(100 * time.Millisecond)

    // Create session 0 using legacy naming, then send output
    if err := exec.Command("tmux", "-S", socketPath, "new-session", "-d", "-s", "sprite-exec-0").Run(); err != nil {
        t.Fatalf("create session 0: %v", err)
    }
    _ = exec.Command("tmux", "-S", socketPath, "send-keys", "-t", "sprite-exec-0", "top", "Enter").Run()

    time.Sleep(1 * time.Second)

    m := NewManager(ctx, Options{SocketPath: socketPath, TmuxBinary: "tmux"})
    m.windowMonitor = wm
    info := m.GetAllSessionActivityInfo()
    if s, ok := info["0"]; ok {
        // The target is that active sessions with output should not be marked inactive
        if !s.IsActive && s.BytesPerSecond > 0 {
            t.Errorf("BUG: session 0 inactive with non-zero data rate: %+v", s)
        }
    } else {
        t.Errorf("session 0 not found; available: %d", len(info))
    }
}


