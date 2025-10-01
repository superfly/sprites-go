package container

import (
	"fmt"
	"os"
	"strconv"
	"strings"
)

// GetContainerPID finds the actual container process PID given a wrapper process PID.
// This is useful when using crun/runc with console-socket, where the command you start
// is a wrapper that spawns the actual container process as its child.
// Returns all child PIDs, not just the first one.
func GetContainerPID(wrapperPID int) (int, error) {
	children, err := getChildProcesses(wrapperPID)
	if err != nil {
		return 0, fmt.Errorf("failed to get child processes: %w", err)
	}

	if len(children) == 0 {
		return 0, fmt.Errorf("no child processes found for PID %d", wrapperPID)
	}

	// For crun/runc, we typically want the first child process
	return children[0], nil
}

// GetAllChildPIDs returns all child process PIDs for a given wrapper PID.
func GetAllChildPIDs(wrapperPID int) ([]int, error) {
	return getChildProcesses(wrapperPID)
}

// getChildProcesses reads the child PIDs of a given parent process.
// This is Linux-specific and reads from /proc/<pid>/task/<pid>/children.
func getChildProcesses(parentPID int) ([]int, error) {
	// Read /proc/<pid>/task/<pid>/children (Linux-specific)
	childrenFile := fmt.Sprintf("/proc/%d/task/%d/children", parentPID, parentPID)
	data, err := os.ReadFile(childrenFile)
	if err != nil {
		return nil, err
	}

	// Parse space-separated PIDs
	childrenStr := strings.TrimSpace(string(data))
	if childrenStr == "" {
		return nil, nil
	}

	pidStrs := strings.Fields(childrenStr)
	pids := make([]int, 0, len(pidStrs))

	for _, pidStr := range pidStrs {
		pid, err := strconv.Atoi(pidStr)
		if err != nil {
			continue
		}
		pids = append(pids, pid)
	}

	return pids, nil
}
