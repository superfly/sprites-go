package tmux

import (
	"fmt"
	"os"
	"os/exec"
	"testing"

	"github.com/superfly/sprite-env/pkg/tap"
)

// startTestTmuxSession creates a new tmux session for testing
func startTestTmuxSession(t *testing.T, sessionName string) (socketName string, cleanup func()) {
	socketName = fmt.Sprintf("tmux-test-%s-%d", sessionName, os.Getpid())

	// Create session with cat command to avoid continuous output
	createCmd := exec.Command("tmux", "-L", socketName, "new-session", "-d", "-s", sessionName, "cat")
	if err := createCmd.Run(); err != nil {
		t.Fatalf("Failed to create tmux session: %v", err)
	}

	cleanup = func() {
		killCmd := exec.Command("tmux", "-L", socketName, "kill-server")
		killCmd.Run()
	}

	return socketName, cleanup
}

// createTestParser creates a parser connected to a real tmux session
func createTestParser(t *testing.T, socketName, sessionName string) *TmuxControlModeParser {
	cmd := exec.Command("tmux", "-L", socketName, "-C", "attach-session", "-t", sessionName)

	// Use discard logger to suppress output
	logger := tap.NewDiscardLogger()

	parser, err := NewTmuxControlModeParser(cmd, logger)
	if err != nil {
		t.Fatalf("Failed to create parser: %v", err)
	}

	return parser
}
