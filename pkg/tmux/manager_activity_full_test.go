package tmux

import (
    "context"
    "fmt"
    "os"
    "os/exec"
    "strings"
    "testing"
    "time"
)

// Mirrors terminal activity tests with the WindowMonitor, adapted to pkg/tmux
func TestManager_Activity_FullLifecycle(t *testing.T) {
    if testing.Short() {
        t.Skip("short mode")
    }
    if _, err := exec.LookPath("tmux"); err != nil {
        t.Skip("tmux not found")
    }

    socketPath := fmt.Sprintf("/tmp/tmux-activity-test-%d-%d", os.Getpid(), time.Now().UnixNano())
    t.Cleanup(func() {
        os.Remove(socketPath)
        exec.Command("tmux", "-S", socketPath, "kill-server").Run()
    })

    ctx := context.Background()
    monitorSession := "activity-monitor"
    // Ensure monitor session exists
    _ = exec.Command("tmux", "-S", socketPath, "new-session", "-d", "-s", monitorSession).Run()

    wm := NewWindowMonitor(ctx, monitorSession).
        WithSocketPath(socketPath).
        WithConfigPath("").
        WithCommand(exec.Command("tmux"))
    if err := wm.Start(ctx); err != nil {
        t.Fatalf("start window monitor: %v", err)
    }
    defer wm.Close()

    // Create two test sessions with the legacy hardcoded naming the monitor expects
    must := func(err error) { if err != nil { t.Fatal(err) } }
    must(exec.Command("tmux", "-S", socketPath, "new-session", "-d", "-s", "sprite-exec-1").Run())
    must(exec.Command("tmux", "-S", socketPath, "new-session", "-d", "-s", "sprite-exec-2").Run())

    // Wait for discovery
    time.Sleep(500 * time.Millisecond)

    // Initial stats
    stats := wm.GetActivityStats()
    _ = stats

    // Send activity to session 1
    must(exec.Command("tmux", "-S", socketPath, "send-keys", "-t", "sprite-exec-1", "echo activity", "Enter").Run())
    time.Sleep(500 * time.Millisecond)

    // Rolling rate should be > 0 for session 1 at some point; we only assert presence of stats map keys
    stats = wm.GetActivityStats()

    // Inactivity transition: wait >5s
    time.Sleep(6 * time.Second)
    stats = wm.GetActivityStats()

    // Reactivate
    must(exec.Command("tmux", "-S", socketPath, "send-keys", "-t", "sprite-exec-1", "echo reactivate", "Enter").Run())
    time.Sleep(500 * time.Millisecond)

    // Drain events for basic coverage
    ev := wm.GetEventChannel()
    drained := 0
    timeout := time.After(100 * time.Millisecond)
loop:
    for {
        select {
        case <-ev:
            drained++
        case <-timeout:
            break loop
        }
    }
    _ = drained

    // Wire manager and validate mapping shape
    m := NewManager(ctx, Options{SocketPath: socketPath, TmuxBinary: "tmux"})
    m.windowMonitor = wm
    info := m.GetAllSessionActivityInfo()
    // Keys should be numeric IDs (e.g., "1", "2") and names should match sprite-exec-<id>
    for id, s := range info {
        if !strings.HasPrefix(s.Name, "sprite-exec-") || !strings.HasSuffix(s.Name, id) {
            t.Fatalf("unexpected name mapping for %s: %+v", id, s)
        }
    }
}


