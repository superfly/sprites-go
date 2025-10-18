package runner

import (
	"bytes"
	"context"
	"os/exec"
	"testing"
	"time"
)

// Ensure that a program that closes stdin early (head -n1) does not deadlock our stdin loop.
func TestNonTTY_StdinEarlyClose(t *testing.T) {
	t.Parallel()
	r := &Runner{}
	cmd := exec.Command("sh", "-c", "head -n1 > /dev/null")
	var out bytes.Buffer
	ctx, cancel := context.WithTimeout(context.Background(), 3*time.Second)
	defer cancel()

	// Provide more data than needed; head should close stdin after the first line
	_, err := r.RunContext(ctx, cmd,
		WithStdout(&out),
		WithStderr(&out),
		WithStdin(bytes.NewBufferString("line1\nline2\nline3\n")),
	)
	if err != nil {
		t.Fatalf("run error: %v", err)
	}
}
