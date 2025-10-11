//go:build linux

package system

import (
	"fmt"
	"os"
	"os/exec"
)

// setContainerHostname sets the hostname inside the container's UTS namespace
// This uses crun exec to run hostname command inside the container
func setContainerHostname(hostname string) error {
	// Use crun exec to run hostname command inside the container
	// The container is named "app" in launch.sh
	cmd := exec.Command("crun", "exec", "app", "hostname", hostname)
	if output, err := cmd.CombinedOutput(); err != nil {
		return fmt.Errorf("failed to set container hostname: %w (output: %s)", err, string(output))
	}

	return nil
}

// getHostname gets the system hostname
func getHostname() (string, error) {
	// Use os.Hostname which works cross-platform
	return os.Hostname()
}
