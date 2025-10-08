package system

import (
	"fmt"
	"os"
	"os/exec"
	"strconv"
	"strings"
)

// SetupCgroups initializes the cgroup v2 filesystem and sets up the initial cgroup hierarchy
func SetupCgroups() error {
	// Check if cgroup2 is mounted
	cmd := exec.Command("mountpoint", "-q", "/sys/fs/cgroup")
	if err := cmd.Run(); err != nil {
		// cgroup2 is not mounted, mount it
		fmt.Println("Mounting cgroup2 filesystem...")
		if err := os.MkdirAll("/sys/fs/cgroup", 0755); err != nil {
			return fmt.Errorf("failed to create cgroup directory: %w", err)
		}

		cmd = exec.Command("mount", "-t", "cgroup2", "-o", "nsdelegate,memory_recursiveprot", "cgroup2", "/sys/fs/cgroup")
		if output, err := cmd.CombinedOutput(); err != nil {
			return fmt.Errorf("failed to mount cgroup2: %w, output: %s", err, output)
		}
	}

	// Create the init cgroup for system processes
	initCgroupPath := "/sys/fs/cgroup/init"
	if err := os.MkdirAll(initCgroupPath, 0755); err != nil {
		return fmt.Errorf("failed to create init cgroup: %w", err)
	}

	// Move all processes from root cgroup to init cgroup
	fmt.Println("Reading PIDs from root cgroup...")
	pidsData, err := os.ReadFile("/sys/fs/cgroup/cgroup.procs")
	if err != nil {
		return fmt.Errorf("failed to read root cgroup PIDs: %w", err)
	}

	// Parse PIDs and move them
	pids := strings.Fields(string(pidsData))
	for _, pid := range pids {
		if pid == "" {
			continue
		}
		// Write PID to init cgroup, ignore errors (process may have exited)
		if err := os.WriteFile("/sys/fs/cgroup/init/cgroup.procs", []byte(pid), 0644); err != nil {
			// Non-fatal, process may have already exited
			continue
		}
	}

	// Read available controllers
	controllersData, err := os.ReadFile("/sys/fs/cgroup/cgroup.controllers")
	if err != nil {
		return fmt.Errorf("failed to read cgroup controllers: %w", err)
	}

	controllers := strings.Fields(string(controllersData))
	enabledControllers := make([]string, 0, len(controllers))

	fmt.Println("Available cgroup controllers:")
	for _, controller := range controllers {
		fmt.Printf("  %s\n", controller)
		enabledControllers = append(enabledControllers, "+"+controller)
	}

	// Enable controllers in root's subtree_control
	if len(enabledControllers) > 0 {
		controlStr := strings.Join(enabledControllers, " ")
		if err := os.WriteFile("/sys/fs/cgroup/cgroup.subtree_control", []byte(controlStr), 0644); err != nil {
			return fmt.Errorf("failed to enable controllers in root cgroup: %w", err)
		}
	}

	// Create containers cgroup
	containersCgroupPath := "/sys/fs/cgroup/containers"
	if err := os.MkdirAll(containersCgroupPath, 0755); err != nil {
		return fmt.Errorf("failed to create containers cgroup: %w", err)
	}

	// Enable controllers in containers' subtree_control
	if len(enabledControllers) > 0 {
		controlStr := strings.Join(enabledControllers, " ")
		if err := os.WriteFile("/sys/fs/cgroup/containers/cgroup.subtree_control", []byte(controlStr), 0644); err != nil {
			return fmt.Errorf("failed to enable controllers in containers cgroup: %w", err)
		}
	}

	// Create juicefs cgroup
	juicefsCgroupPath := "/sys/fs/cgroup/juicefs"
	if err := os.MkdirAll(juicefsCgroupPath, 0755); err != nil {
		return fmt.Errorf("failed to create juicefs cgroup: %w", err)
	}

	// Create litestream cgroup
	litestreamCgroupPath := "/sys/fs/cgroup/litestream"
	if err := os.MkdirAll(litestreamCgroupPath, 0755); err != nil {
		return fmt.Errorf("failed to create litestream cgroup: %w", err)
	}

	fmt.Println("Cgroup setup completed successfully")
	return nil
}

// MovePid moves a process and all its descendants to the specified cgroup
func MovePid(pid int, cgroupName string) error {
	cgroupPath := fmt.Sprintf("/sys/fs/cgroup/%s", cgroupName)

	// Check if cgroup exists
	if _, err := os.Stat(cgroupPath); os.IsNotExist(err) {
		return fmt.Errorf("cgroup %s does not exist", cgroupName)
	}

	// Move the main process to the cgroup
	procsFile := fmt.Sprintf("%s/cgroup.procs", cgroupPath)
	if err := os.WriteFile(procsFile, []byte(fmt.Sprintf("%d", pid)), 0644); err != nil {
		return fmt.Errorf("failed to move pid %d to cgroup %s: %w", pid, cgroupName, err)
	}

	fmt.Printf("Moved PID %d to cgroup %s\n", pid, cgroupName)

	// Find and move all descendant processes
	descendants, err := getDescendantPids(pid)
	if err != nil {
		// Non-fatal - log and continue
		fmt.Printf("Warning: failed to get descendants of PID %d: %v\n", pid, err)
		return nil
	}

	for _, descendant := range descendants {
		if err := os.WriteFile(procsFile, []byte(fmt.Sprintf("%d", descendant)), 0644); err != nil {
			// Non-fatal - process may have exited
			fmt.Printf("Warning: failed to move descendant PID %d to cgroup %s: %v\n", descendant, cgroupName, err)
			continue
		}
		fmt.Printf("Moved descendant PID %d to cgroup %s\n", descendant, cgroupName)
	}

	return nil
}

// getDescendantPids returns all descendant PIDs of the given PID
func getDescendantPids(pid int) ([]int, error) {
	descendants := make([]int, 0)
	visited := make(map[int]bool)

	var findDescendants func(int) error
	findDescendants = func(parentPid int) error {
		if visited[parentPid] {
			return nil
		}
		visited[parentPid] = true

		// Read the children file for this PID
		childrenFile := fmt.Sprintf("/proc/%d/task/%d/children", parentPid, parentPid)
		data, err := os.ReadFile(childrenFile)
		if err != nil {
			// Process may have exited or file doesn't exist
			return nil
		}

		// Parse PIDs from the children file
		childPids := strings.Fields(string(data))
		for _, pidStr := range childPids {
			if pidStr == "" {
				continue
			}
			childPid, err := strconv.Atoi(pidStr)
			if err != nil {
				continue
			}
			// Check if we've already visited this child to prevent infinite recursion
			if visited[childPid] {
				continue
			}
			descendants = append(descendants, childPid)
			// Recursively find descendants of this child
			if err := findDescendants(childPid); err != nil {
				return err
			}
		}

		return nil
	}

	if err := findDescendants(pid); err != nil {
		return nil, err
	}

	return descendants, nil
}
