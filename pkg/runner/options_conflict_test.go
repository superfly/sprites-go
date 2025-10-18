package runner

import (
	"bytes"
	"context"
	"os"
	"os/exec"
	"testing"
)

func TestOptions_Conflicts(t *testing.T) {
	r := &Runner{}
	var out bytes.Buffer

	// TTY + Stderr is allowed (stderr may capture non-PTY stderr like tmux)
	if _, err := r.Run(exec.Command("true"), WithStdout(&out), WithStderr(&out), WithNewTTY()); err != nil {
		t.Fatalf("unexpected error for TTY+stderr: %v", err)
	}

	// Multiple TTY modes conflict
	if _, err := r.Run(exec.Command("true"), WithStdout(&out), WithNewTTY(), WithWaitTTY(func(ctx context.Context) (*os.File, error) { return nil, nil })); err == nil {
		t.Fatalf("expected error for conflicting TTY options")
	}
}
