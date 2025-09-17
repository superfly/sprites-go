package container

import (
	"fmt"
	"os"
	"strconv"
	"strings"
)

// ResolvePID finds the host PID for a given container PID.
// It scans /proc to find a process whose namespace PID matches the given container PID.
func ResolvePID(containerPID int) (int, error) {
	// Open /proc directory
	procDir, err := os.Open("/proc")
	if err != nil {
		return 0, fmt.Errorf("failed to open /proc: %w", err)
	}
	defer procDir.Close()

	// Read all entries
	entries, err := procDir.Readdir(-1)
	if err != nil {
		return 0, fmt.Errorf("failed to read /proc: %w", err)
	}

	// Check each PID directory
	for _, entry := range entries {
		// Skip non-PID entries
		hostPID, err := strconv.Atoi(entry.Name())
		if err != nil {
			continue
		}

		// Check if this process has the namespace PID we're looking for
		nsPID, err := getNamespacePID(hostPID)
		if err != nil {
			continue // Skip if we can't read this process
		}

		if nsPID == containerPID {
			return hostPID, nil
		}
	}

	return 0, fmt.Errorf("container PID %d not found in any namespace", containerPID)
}

// getNamespacePID reads the namespace PID from /proc/PID/status
// The NSpid line shows: NSpid: <host_pid> <ns_pid>
func getNamespacePID(hostPID int) (int, error) {
	statusPath := fmt.Sprintf("/proc/%d/status", hostPID)
	data, err := os.ReadFile(statusPath)
	if err != nil {
		return 0, err
	}

	lines := strings.Split(string(data), "\n")
	for _, line := range lines {
		if strings.HasPrefix(line, "NSpid:") {
			fields := strings.Fields(line)
			if len(fields) >= 3 {
				// fields[0] is "NSpid:", fields[1] is host PID, fields[2] is namespace PID
				nsPID, err := strconv.Atoi(fields[2])
				if err != nil {
					return 0, err
				}
				return nsPID, nil
			} else if len(fields) == 2 {
				// No namespace PID means this process is not in a PID namespace
				return hostPID, nil
			}
		}
	}

	// If no NSpid line found, process is not in a namespace
	return hostPID, nil
}
