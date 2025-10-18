package tests

import (
	"bufio"
	"context"
	"fmt"
	"strings"
	"testing"
	"time"

	sprites "github.com/superfly/sprites-go"
)

// TestExecDetachableTTY ensures a TTY detachable session is created and listed
func TestExecDetachableTTY(t *testing.T) {
	_, cancel := SetTestDeadlineWithTimeout(t, 60*time.Second)
	defer cancel()

	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Configure and start the system with API enabled
	config := TestConfig(testDir)
	// Ensure container execution is disabled for this test so tmux runs on host
	config.ContainerEnabled = false
	SetupTestPorts(t, config)

	sys, cleanup, err := TestSystem(t, config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	if err := sys.Start(); err != nil {
		t.Fatalf("Failed to start system: %v", err)
	}

	// Ensure process is running so /exec passes middleware
	if err := sys.WhenProcessRunning(t.Context()); err != nil {
		t.Fatalf("Process did not start: %v", err)
	}

	// Build SDK client pointing at this system's API
	baseURL := fmt.Sprintf("http://%s", config.APIListenAddr)
	client := sprites.New(config.APIToken, sprites.WithBaseURL(baseURL))
	sprite := client.Sprite("local-test-sprite")

	// Start an interactive shell (clean, predictable)
	cmd := sprite.Command("/bin/bash", "--noprofile", "--norc", "-i")
	cmd.SetDetachable(true)
	_ = cmd.SetTTYSize(24, 80)

	// Prepare IO
	stdin, err := cmd.StdinPipe()
	if err != nil {
		t.Fatalf("StdinPipe failed: %v", err)
	}
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		t.Fatalf("StdoutPipe failed: %v", err)
	}

	// Start the shell
	if err := cmd.Start(); err != nil {
		t.Fatalf("failed to start interactive shell: %v", err)
	}

	// Reader and a small collector goroutine
	reader := bufio.NewReader(stdout)
	outCh := make(chan string, 64)
	doneCh := make(chan struct{})
	go func() {
		defer close(doneCh)
		for {
			s, err := reader.ReadString('\n')
			if s != "" {
				outCh <- s
			}
			if err != nil {
				return
			}
		}
	}()

	// Helper to wait for substring in output stream
	waitFor := func(substr string, timeout time.Duration) error {
		deadline := time.Now().Add(timeout)
		var b strings.Builder
		for time.Now().Before(deadline) {
			select {
			case s := <-outCh:
				b.WriteString(s)
				if strings.Contains(b.String(), substr) {
					return nil
				}
			case <-time.After(50 * time.Millisecond):
			}
		}
		return fmt.Errorf("timeout waiting for %q in output: %q", substr, b.String())
	}

	// Send a marker to confirm interactivity
	_, _ = stdin.Write([]byte("echo READY\n"))
	if err := waitFor("READY", 5*time.Second); err != nil {
		t.Fatalf("did not see READY echo: %v", err)
	}

	// Poll briefly for session to appear
	deadline := time.Now().Add(3 * time.Second)
	for {
		ctx, cancelList := context.WithTimeout(context.Background(), 2*time.Second)
		sessions, err := client.ListSessions(ctx, sprite.Name())
		cancelList()
		if err != nil {
			t.Fatalf("ListSessions failed: %v", err)
		}
		if len(sessions) > 0 {
			break
		}
		if time.Now().After(deadline) {
			t.Fatalf("expected at least one tmux session, got 0")
		}
		time.Sleep(100 * time.Millisecond)
	}
}
