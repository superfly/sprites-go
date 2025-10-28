//go:build linux
// +build linux

package overlay

import (
	"fmt"
	"os/exec"
	"strings"
	"testing"
	"time"
)

// VerifyNoTestOverlays checks that no test-related overlays or loop devices remain
// This should be called after cleanup to ensure no resources leaked
func VerifyNoTestOverlays(t *testing.T, m *Manager) {
	t.Helper()

	if m == nil {
		return
	}

	// Allow brief settling time in CI where losetup/mount state can lag
	// Retry for up to ~3s before declaring failure
	var failures []string
	for attempt := 0; attempt < 60; attempt++ {
		failures = failures[:0]

		// Check if overlay is still mounted
		if m.IsOverlayFSMounted() {
			failures = append(failures, fmt.Sprintf("OverlayFS still mounted at %s", m.overlayTargetPath))
		}

		// Check if loop device mount is still present
		if m.IsMounted() {
			failures = append(failures, fmt.Sprintf("Loop device still mounted at %s", m.mountPath))
		}

		// Check for our specific loop devices by checking if our image file is attached
		imagePath := m.GetImagePath()
		if output, err := exec.Command("losetup", "-a").Output(); err == nil {
			loopList := string(output)
			for _, line := range strings.Split(loopList, "\n") {
				if line == "" {
					continue
				}
				if strings.Contains(line, imagePath) {
					failures = append(failures, fmt.Sprintf("Loop device still attached to our image: %s", line))
				}
			}
		}

		// Check for mount entries for our paths
		if output, err := exec.Command("mount").Output(); err == nil {
			mountOutput := string(output)
			for _, line := range strings.Split(mountOutput, "\n") {
				if line == "" {
					continue
				}
				if strings.Contains(line, " on "+m.overlayTargetPath+" type ") {
					failures = append(failures, fmt.Sprintf("Mount still present: %s", line))
				}
				if strings.Contains(line, " on "+m.mountPath+" type ") {
					failures = append(failures, fmt.Sprintf("Mount still present: %s", line))
				}
			}
		}

		if len(failures) == 0 {
			return
		}
		time.Sleep(50 * time.Millisecond)
	}

	// Fail the test if any issues remain after retries
	t.Errorf("Overlay cleanup verification FAILED:")
	for _, failure := range failures {
		t.Errorf("  - %s", failure)
	}
}
