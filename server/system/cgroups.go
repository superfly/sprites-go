package system

import (
	"fmt"
	"os"
	"os/exec"
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

	fmt.Println("Cgroup setup completed successfully")
	return nil
}
