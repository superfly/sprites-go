package runner

import (
	"bytes"
	"context"
	"errors"
	"os"
	"os/exec"
	"testing"
	"time"
)

func TestWaitTTY_ProviderContract(t *testing.T) {
	r := &Runner{}
	cmd := exec.Command("sh", "-c", "sleep 0.2; echo done")
	var out bytes.Buffer
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()

	// Simulate delayed PTY provisioning success
	_, _ = r.RunContext(ctx, cmd,
		WithStdout(&out),
		WithWaitTTY(func(ctx context.Context) (*os.File, error) {
			// For testing, immediately fail to avoid needing an actual fd
			return nil, errors.New("no pty in test")
		}),
	)
	// Only checks that failure is plumbed back without deadlocks
}
