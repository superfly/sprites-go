//go:build !windows

package runner

import (
	"context"
	"os/exec"
)

// runWithoutTTY executes the command without a PTY using direct stdout/stderr writers
// and a dedicated stdin loop for cancellation.
func runWithoutTTY(ctx context.Context, cmd *exec.Cmd, cfg *runConfig) (int, error) {
	// Retained only for legacy tests using synchronous API
	r, err := NewWithContext(ctx, cmd, WithStdout(cfg.stdout), WithStderr(cfg.stderr), WithStdin(cfg.stdin))
	if err != nil {
		return -1, err
	}
	if err := r.Start(); err != nil {
		return -1, err
	}
	if err := r.Wait(); err != nil {
		if ee, ok := err.(*exec.ExitError); ok {
			return ee.ExitCode(), nil
		}
		return -1, err
	}
	return r.ExitCode(), nil
}
