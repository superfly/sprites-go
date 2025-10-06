package juicefs

import (
	"context"
	"fmt"
	"os/exec"
	"strings"
	"testing"
	"time"
)

// CleanupTestJuiceFS unmounts JuiceFS and verifies cleanup
// Call this in a defer at the start of tests that manage mounts
func CleanupTestJuiceFS(t *testing.T, jfs *JuiceFS) {
	t.Helper()

	if jfs == nil {
		return
	}

	// Try to stop JuiceFS
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
	defer cancel()
	_ = jfs.Stop(ctx)

	// Verify cleanup
	VerifyNoTestJuiceFS(t, jfs)
}

// VerifyNoTestJuiceFS checks that no test-related JuiceFS mounts remain
// This should be called after cleanup to ensure no resources leaked
func VerifyNoTestJuiceFS(t *testing.T, jfs *JuiceFS) {
	t.Helper()

	if jfs == nil {
		return
	}

	var failures []string

	// Check if JuiceFS is still mounted using the manager's method
	if jfs.IsMounted() {
		failures = append(failures, "JuiceFS reports it is still mounted")
	}

	// Get the mount path and check system mounts
	mountPath := jfs.GetMountPath()
	if mountPath == "" {
		// Can't verify without knowing the mount path
		return
	}

	// Check mount table for our JuiceFS mount
	if output, err := exec.Command("mount").Output(); err == nil {
		mountOutput := string(output)
		for _, line := range strings.Split(mountOutput, "\n") {
			if line == "" {
				continue
			}
			// Check for JuiceFS/SpriteFS mounts at our mount path
			if strings.Contains(line, " on "+mountPath+" ") &&
				(strings.Contains(line, "type fuse.juicefs") || strings.Contains(line, "SpriteFS on")) {
				failures = append(failures, fmt.Sprintf("JuiceFS mount still present: %s", line))
			}
		}
	}

	// Fail the test if any issues found
	if len(failures) > 0 {
		t.Errorf("JuiceFS cleanup verification FAILED:")
		for _, failure := range failures {
			t.Errorf("  - %s", failure)
		}
	}
}
