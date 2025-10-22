package tmux

import (
	"context"
	"os/exec"
	"strings"
	"testing"
)

// Covers argv construction, prefixing, and control mode flags
func TestManager_Args_PrefixingAndControlMode(t *testing.T) {
	m := NewManager(context.Background(), Options{
		TmuxBinary:    "/bin/echo",
		SocketPath:    "/tmp/mux.sock",
		ConfigPath:    "/etc/tmux.conf",
		SessionPrefix: "sprites",
	})

	base := exec.Command("/bin/sh", "-c", "echo hi")
	cmd, id := m.NewSessionCmd(base, true)
	if id == "" {
		t.Fatalf("expected generated id")
	}
	joined := strings.Join(cmd.Args, " ")
	if !strings.Contains(joined, "-f /etc/tmux.conf") || !strings.Contains(joined, "-S /tmp/mux.sock") {
		t.Fatalf("missing config/socket in args: %v", cmd.Args)
	}
	if !strings.Contains(joined, "-CC") {
		t.Fatalf("expected -CC for control mode: %v", cmd.Args)
	}
	if !strings.Contains(joined, "new -s sprites-exec-"+id) {
		t.Fatalf("expected new-session with prefixed name, got: %v", cmd.Args)
	}
	// We now only pass a generated wrapper script path to tmux new-session,
	// not the base command path directly.
	if !strings.Contains(joined, "/.sprite/tmp/exec-"+id) {
		t.Fatalf("expected wrapper script path with id, got: %v", cmd.Args)
	}

	attach := m.AttachCmd(id, true)
	aj := strings.Join(attach.Args, " ")
	if !strings.Contains(aj, "attach -t sprites-exec-"+id) {
		t.Fatalf("expected attach-session targeting prefixed name, got: %v", attach.Args)
	}
	if !strings.Contains(aj, "-CC") {
		t.Fatalf("expected -CC in attach args: %v", attach.Args)
	}
}
