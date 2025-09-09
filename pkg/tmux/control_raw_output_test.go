package tmux

import (
	"bufio"
	"fmt"
	"io"
	"os"
	"os/exec"
	"strings"
	"testing"
	"time"
)

// TestControlModeOutput captures real tmux control mode output for reference
func TestControlModeOutput(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping control mode output test in short mode")
	}

	socketName := fmt.Sprintf("tmux-test-output-%d", os.Getpid())

	// Create session with a command that doesn't generate continuous output
	createCmd := exec.Command("tmux", "-L", socketName, "new-session", "-d", "-s", "output-test", "cat")
	if err := createCmd.Run(); err != nil {
		t.Fatalf("Failed to create tmux session: %v", err)
	}

	defer func() {
		killCmd := exec.Command("tmux", "-L", socketName, "kill-server")
		killCmd.Run()
	}()

	// Attach in control mode
	cmd := exec.Command("tmux", "-L", socketName, "-C", "attach-session", "-t", "output-test")

	stdin, err := cmd.StdinPipe()
	if err != nil {
		t.Fatal(err)
	}

	stdout, err := cmd.StdoutPipe()
	if err != nil {
		t.Fatal(err)
	}

	if err := cmd.Start(); err != nil {
		t.Fatal(err)
	}

	// Read all output
	output := make(chan string, 100)
	go func() {
		reader := bufio.NewReader(stdout)
		for {
			line, err := reader.ReadString('\n')
			if err != nil {
				if err != io.EOF {
					t.Logf("Read error: %v", err)
				}
				close(output)
				return
			}

			line = strings.TrimRight(line, "\n\r")
			if line != "" {
				output <- line
			}
		}
	}()

	// Helper to drain output
	drainOutput := func(duration time.Duration) []string {
		var lines []string
		timeout := time.After(duration)
		for {
			select {
			case line, ok := <-output:
				if !ok {
					return lines
				}
				lines = append(lines, line)
				t.Logf("Output: %s", line)
			case <-timeout:
				return lines
			}
		}
	}

	// Initial output
	t.Log("=== Initial connection ===")
	drainOutput(200 * time.Millisecond)

	// Test commands
	tests := []struct {
		name    string
		command string
	}{
		{"list-sessions", "list-sessions -F '#{session_id} #{session_name}'"},
		{"list-windows", "list-windows -F '#{window_id} #{window_name}'"},
		{"list-panes", "list-panes -F '#{pane_id} #{window_id} #{pane_index}'"},
		{"new-window", "new-window -n test-window"},
		{"rename-window", "rename-window -t test-window renamed-window"},
		{"send-keys", "send-keys -t renamed-window 'echo hello' Enter"},
		{"split-window", "split-window -t renamed-window -v"},
	}

	for _, test := range tests {
		t.Logf("=== Sending: %s ===", test.name)
		fmt.Fprintln(stdin, test.command)

		lines := drainOutput(300 * time.Millisecond)

		if len(lines) == 0 {
			t.Errorf("No output for command: %s", test.name)
		}
	}

	// Detach
	fmt.Fprintln(stdin, "detach-client")
	drainOutput(100 * time.Millisecond)

	stdin.Close()
	cmd.Process.Kill()
	cmd.Wait()
}
