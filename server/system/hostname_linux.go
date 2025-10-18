//go:build linux

package system

import (
	"encoding/json"
	"fmt"
	"os"
	"os/exec"
)

// setContainerHostname sets the hostname inside the container's UTS namespace
// This uses crun exec to run hostname command inside the container
func setContainerHostname(hostname string) error {
	// First check if the container is running
	stateCmd := exec.Command("crun", "state", "app")
	stateOutput, err := stateCmd.CombinedOutput()
	if err != nil {
		return fmt.Errorf("container not ready: %w (output: %s)", err, string(stateOutput))
	}

	// Parse the state JSON to check if container is running
	var state struct {
		Status string `json:"status"`
	}
	if err := json.Unmarshal(stateOutput, &state); err != nil {
		return fmt.Errorf("failed to parse container state: %w", err)
	}

	if state.Status != "running" {
		return fmt.Errorf("container is not running (status: %s)", state.Status)
	}

	// Container is running, set the hostname
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
