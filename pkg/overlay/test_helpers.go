//go:build linux
// +build linux

package overlay

import (
	"fmt"
	"os/exec"
	"strings"
	"testing"
)

// VerifyNoTestOverlays checks that no test-related overlays or loop devices remain
// This should be called after cleanup to ensure no resources leaked
func VerifyNoTestOverlays(t *testing.T, m *Manager) {
	t.Helper()

	if m == nil {
		return
	}

	var failures []string

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
			// Check if this loop device references our image file
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
			// Check for our overlay target path
			if strings.Contains(line, " on "+m.overlayTargetPath+" type ") {
				failures = append(failures, fmt.Sprintf("Mount still present: %s", line))
			}
			// Check for our mount path
			if strings.Contains(line, " on "+m.mountPath+" type ") {
				failures = append(failures, fmt.Sprintf("Mount still present: %s", line))
			}
		}
	}

	// Fail the test if any issues found
	if len(failures) > 0 {
		t.Errorf("Overlay cleanup verification FAILED:")
		for _, failure := range failures {
			t.Errorf("  - %s", failure)
		}
	}
}
