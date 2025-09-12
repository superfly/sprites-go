package container

import (
	"encoding/json"
	"fmt"
	"io"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"syscall"
	"time"

	"github.com/superfly/sprite-env/pkg/supervisor"
)

// ProcessConfig extends supervisor.Config with optional TTY timeout
type ProcessConfig struct {
	supervisor.Config

	// TTYTimeout specifies how long to wait for the TTY from the process
	// Defaults to 5 seconds if not set
	// Only used when containers are enabled system-wide
	TTYTimeout time.Duration

	// TTYOutput specifies where to forward TTY output
	// If nil, no TTY forwarding is performed
	// Commonly set to os.Stdout to forward container output to logs
	TTYOutput io.Writer
}

// Process wraps a supervisor with TTY management
type Process struct {
	*supervisor.Supervisor
	tty          *Tty
	config       ProcessConfig
	containerPID int           // PID of the actual container process (not the crun wrapper)
	containerID  string        // ID of the container for cleanup operations
	readyCh      chan struct{} // Signals when container is ready (PTY received)
}

// NewProcess creates a new process with automatic container support based on system config
func NewProcess(config ProcessConfig) (*Process, error) {
	var tty *Tty

	// Check if containers are enabled system-wide
	if IsEnabled() {
		// Generate a unique socket path in the configured directory
		socketPath := fmt.Sprintf("%s/container-process-%d-%d.sock",
			GetSocketDir(), os.Getpid(), time.Now().UnixNano())

		if config.Logger != nil {
			config.Logger.Info("Container support enabled, creating TTY manager",
				"socketPath", socketPath,
				"command", config.Command,
				"args", config.Args)
		}

		// Create TTY manager
		var err error
		tty, err = NewWithPath(socketPath)
		if err != nil {
			return nil, fmt.Errorf("failed to create TTY manager: %w", err)
		}

		// Add CONSOLE_SOCKET to environment
		if config.Env == nil {
			config.Env = os.Environ()
		}
		config.Env = append(config.Env, fmt.Sprintf("CONSOLE_SOCKET=%s", socketPath))

		if config.Logger != nil {
			config.Logger.Info("Added CONSOLE_SOCKET to environment",
				"CONSOLE_SOCKET", socketPath)
		}

		// Note: CONTAINER_WRAPPED env var is set later only for actual container processes

		// Ensure we clean up socket on failure
		defer func() {
			if err != nil && tty != nil {
				tty.Close()
			}
		}()
	}

	// Create supervisor with the modified config
	supervisor, err := supervisor.New(config.Config)
	if err != nil {
		if tty != nil {
			tty.Close()
		}
		return nil, fmt.Errorf("failed to create supervisor: %w", err)
	}

	// Extract container ID from command
	var containerID string
	if tty != nil {
		containerID = extractContainerID(config.Command, config.Args)

		// Add CONTAINER_WRAPPED env var since this is a container process
		config.Env = append(config.Env, "CONTAINER_WRAPPED=true")
		if config.Logger != nil {
			config.Logger.Info("Container process configured",
				"containerID", containerID,
				"command", config.Command,
				"socketPath", tty.SocketPath())
		}
	}

	return &Process{
		Supervisor:  supervisor,
		tty:         tty,
		config:      config,
		containerID: containerID,
		readyCh:     make(chan struct{}),
	}, nil
}

// extractContainerID attempts to extract the container ID from command and args
func extractContainerID(command string, args []string) string {
	// For base-env/exec.sh and launch.sh, the container ID is hardcoded as "app"
	if strings.Contains(command, "exec.sh") || strings.Contains(command, "/exec.sh") ||
		strings.Contains(command, "launch.sh") || strings.Contains(command, "/launch.sh") {
		return "app"
	}

	// For direct crun commands, look for the container ID argument
	if strings.Contains(command, "crun") || strings.Contains(command, "runc") {
		// Look for patterns like: crun run <container-id> or crun exec <container-id>
		for i, arg := range args {
			if (arg == "run" || arg == "exec") && i+1 < len(args) {
				return args[i+1]
			}
		}
	}

	// Default container ID
	return "app"
}

// Start starts the process and returns its PID
func (p *Process) Start() (int, error) {
	if p.config.Logger != nil {
		p.config.Logger.Debug("Process.Start called",
			"command", p.config.Command,
			"args", p.config.Args,

			"hasTTY", p.tty != nil,
			"containerID", p.containerID)
	}

	// Start the process using supervisor
	pid, err := p.Supervisor.Start()
	if err != nil {
		return -1, err
	}

	// Start TTY forwarding if configured and containers are enabled
	if p.config.TTYOutput != nil && p.tty != nil {
		go p.forwardTTY()
	} else if p.tty != nil {
		// For processes without TTY output, immediately signal ready
		// and handle PTY in the background
		go func() {
			if p.config.Logger != nil {
				p.config.Logger.Debug("Starting PTY handler for container process (no-wait mode)",
					"containerID", p.containerID,
					"socketPath", p.tty.SocketPath())
			}

			pty, err := p.GetTTY()
			if err != nil {
				if p.config.Logger != nil {
					p.config.Logger.Warn("Container PTY wait failed (non-TTY mode)",
						"error", err,
						"containerID", p.containerID,
						"socketPath", p.tty.SocketPath())
				}
				return
			}
			defer pty.Close()

			// Discard output since no TTYOutput is configured
			go io.Copy(io.Discard, pty)
		}()

		// Signal ready immediately
		select {
		case <-p.readyCh:
			// Already closed
		default:
			close(p.readyCh)
		}
	}

	return pid, nil
}

// Signal overrides the supervisor's Signal method to target the container process when appropriate
func (p *Process) Signal(sig os.Signal) error {
	// If we have a container PID, signal it directly
	if p.containerPID > 0 {
		if p.config.Logger != nil {
			p.config.Logger.Info("Signaling internal container process",
				"signal", sig,
				"containerPID", p.containerPID,
				"action", "direct_syscall_kill")
		}
		return syscall.Kill(p.containerPID, sig.(syscall.Signal))
	}

	// Fall back to supervisor's signal method
	if p.config.Logger != nil {
		wrapperPID, _ := p.Supervisor.Pid()
		p.config.Logger.Info("Signaling wrapper process (no container PID found)",
			"signal", sig,
			"wrapperPID", wrapperPID,
			"action", "supervisor_signal")
	}
	return p.Supervisor.Signal(sig)
}

// findContainerProcess attempts to find the actual container process PID
func (p *Process) findContainerProcess() {
	wrapperPID, err := p.Supervisor.Pid()
	if err != nil {
		if p.config.Logger != nil {
			p.config.Logger.Warn("Could not get wrapper PID", "error", err)
		}
		return
	}

	if p.config.Logger != nil {
		p.config.Logger.Debug("Looking for container process", "wrapperPID", wrapperPID)
	}

	// Use the shared GetContainerPID function
	containerPID, err := GetContainerPID(wrapperPID)
	if err != nil {
		if p.config.Logger != nil {
			p.config.Logger.Warn("Failed to find container process", "error", err, "wrapperPID", wrapperPID)
		}
		return
	}

	p.containerPID = containerPID
	if p.config.Logger != nil {
		p.config.Logger.Debug("Successfully discovered container process",
			"containerPID", p.containerPID,
			"wrapperPID", wrapperPID)
	}
}

// getChildProcesses returns the PIDs of direct child processes
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

// GetContainerPID finds the actual container process PID given a wrapper process PID.
// This is useful when using crun/runc with console-socket, where the command you start
// is a wrapper that spawns the actual container process as its child.
// Returns the first child PID if found, or an error if no children exist.
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

// HostPID converts a container PID to the corresponding host PID.
// containerPID is the PID as seen inside the container.
// containerInitPID is the host PID of the container's init process (PID 1 inside container).
// Returns the host PID, or an error if the process cannot be found.
func HostPID(containerPID, containerInitPID int) (int, error) {
	// Special case: PID 1 in container maps to containerInitPID
	if containerPID == 1 {
		return containerInitPID, nil
	}

	// Read the container's process tree from /proc/<containerInitPID>/root/proc
	// This gives us the view from inside the container
	procPath := fmt.Sprintf("/proc/%d/root/proc/%d/stat", containerInitPID, containerPID)

	// Check if the process exists in the container
	if _, err := os.Stat(procPath); os.IsNotExist(err) {
		return 0, fmt.Errorf("container PID %d not found in container with init PID %d", containerPID, containerInitPID)
	}

	// Read the status file to get the process info
	statusPath := fmt.Sprintf("/proc/%d/root/proc/%d/status", containerInitPID, containerPID)
	data, err := os.ReadFile(statusPath)
	if err != nil {
		return 0, fmt.Errorf("failed to read container process status: %w", err)
	}

	// Parse the NSpid line which shows PID mappings across namespaces
	// Format: NSpid: <PID in innermost namespace> <PID in parent namespace> ... <PID in root namespace>
	lines := strings.Split(string(data), "\n")
	for _, line := range lines {
		if strings.HasPrefix(line, "NSpid:") {
			fields := strings.Fields(line)
			if len(fields) >= 2 {
				// The last field is the host PID
				hostPIDStr := fields[len(fields)-1]
				hostPID, err := strconv.Atoi(hostPIDStr)
				if err != nil {
					return 0, fmt.Errorf("failed to parse host PID: %w", err)
				}
				return hostPID, nil
			}
		}
	}

	return 0, fmt.Errorf("could not find NSpid mapping for container PID %d", containerPID)
}

// cleanupContainer runs crun delete -f to clean up orphaned containers
func (p *Process) cleanupContainer() {
	if p.containerID == "" {
		return
	}

	if p.config.Logger != nil {
		p.config.Logger.Info("Cleaning up orphaned container",
			"containerID", p.containerID,
			"action", "crun_delete_force")
	}

	// Run crun delete -f <container-id>
	cmd := exec.Command("crun", "delete", "-f", p.containerID)
	if err := cmd.Run(); err != nil {
		if p.config.Logger != nil {
			p.config.Logger.Warn("Failed to clean up container",
				"containerID", p.containerID,
				"error", err)
		}
	} else {
		if p.config.Logger != nil {
			p.config.Logger.Info("Successfully cleaned up orphaned container",
				"containerID", p.containerID)
		}
	}
}

// forwardTTY forwards TTY output to the configured writer
func (p *Process) forwardTTY() {
	// Signal ready immediately - don't wait for first byte
	select {
	case <-p.readyCh:
		// Already closed
	default:
		close(p.readyCh)
	}

	pty, err := p.GetTTY()
	if err != nil {
		// TTY forwarding failed, but don't crash the process
		if p.config.Logger != nil {
			p.config.Logger.Warn("Failed to get PTY for forwarding", "error", err)
		}
		return
	}
	defer pty.Close()

	if p.config.Logger != nil {
		p.config.Logger.Debug("Starting PTY forwarding")
	}

	// Forward PTY output to the configured writer
	io.Copy(p.config.TTYOutput, pty)
}

// GetTTY waits for and returns the TTY file descriptor
// This should be called after Start() when containers are enabled system-wide
func (p *Process) GetTTY() (*os.File, error) {
	if p.tty == nil {
		return nil, fmt.Errorf("TTY not enabled for this process")
	}

	timeout := p.config.TTYTimeout
	if timeout == 0 {
		timeout = 5 * time.Second
	}

	if p.config.Logger != nil {
		p.config.Logger.Debug("GetTTY: Waiting for PTY from container",
			"timeout", timeout,
			"socketPath", p.tty.SocketPath(),
			"containerID", p.containerID)
	}

	pty, err := p.tty.GetWithTimeout(timeout)
	if err != nil {
		if p.config.Logger != nil {
			p.config.Logger.Error("GetTTY: Failed to get PTY",
				"error", err,
				"timeout", timeout,
				"socketPath", p.tty.SocketPath(),
				"containerID", p.containerID)
		}
		return nil, err
	}

	// If we don't have the container PID yet,
	// discover it now that the container is running and connected
	if p.containerPID == 0 {
		if p.config.Logger != nil {
			p.config.Logger.Debug("Attempting to find container PID",
				"currentContainerPID", p.containerPID)
		}
		p.findContainerProcess()
	} else if p.config.Logger != nil {
		p.config.Logger.Debug("Skipping container PID discovery",

			"currentContainerPID", p.containerPID)
	}

	return pty, nil
}

// TTYPath returns the socket path if TTY is enabled
func (p *Process) TTYPath() (string, error) {
	if p.tty == nil {
		return "", fmt.Errorf("TTY not enabled for this process")
	}

	return p.tty.SocketPath(), nil
}

// WaitReady waits for the container to be ready (PTY received)
func (p *Process) WaitReady(timeout time.Duration) error {
	if p.config.Logger != nil {
		p.config.Logger.Debug("WaitReady called",
			"timeout", timeout,
			"hasTTY", p.tty != nil,
			"containerID", p.containerID,
			"command", p.config.Command,
			"args", p.config.Args)
	}

	if p.tty == nil {
		// No TTY manager, nothing to wait for
		if p.config.Logger != nil {
			p.config.Logger.Debug("WaitReady: No TTY manager, returning immediately")
		}
		return nil
	}

	timer := time.NewTimer(timeout)
	defer timer.Stop()

	select {
	case <-p.readyCh:
		return nil
	case <-timer.C:
		return fmt.Errorf("timeout waiting for container to be ready after %v", timeout)
	}
}

// Stop gracefully stops the process and cleans up resources
func (p *Process) Stop() error {
	// Implement custom graceful shutdown with container cleanup
	if p.containerID != "" {
		return p.stopContainerProcess()
	}

	// For non-container processes, use the standard supervisor stop logic
	err := p.Supervisor.Stop()

	// Clean up TTY resources after stopping the process
	if p.tty != nil {
		if closeErr := p.tty.Close(); closeErr != nil && err == nil {
			err = closeErr
		}
	}

	return err
}

// stopContainerProcess implements custom graceful shutdown for container processes
func (p *Process) stopContainerProcess() error {

	if p.config.Logger != nil {
		p.config.Logger.Info("Stopping container process with custom logic",
			"containerID", p.containerID)
	}

	// Get the grace period from supervisor config
	gracePeriod := p.config.GracePeriod
	if gracePeriod <= 0 {
		gracePeriod = 10 * time.Second
	}

	// First, try SIGTERM
	if err := p.Signal(syscall.SIGTERM); err != nil {
		if p.config.Logger != nil {
			p.config.Logger.Warn("Failed to send SIGTERM", "error", err)
		}
	}

	// Wait for graceful shutdown or timeout
	exitCh := make(chan error, 1)
	go func() {
		exitCh <- p.Supervisor.Wait()
	}()

	select {
	case err := <-exitCh:
		// Process exited gracefully
		if p.config.Logger != nil {
			p.config.Logger.Info("Container process exited gracefully")
		}

		// Clean up TTY resources
		if p.tty != nil {
			if closeErr := p.tty.Close(); closeErr != nil && err == nil {
				err = closeErr
			}
		}
		// Don't return an error if the process was terminated by our signal
		// (which is expected behavior when we stop it)
		if err != nil {
			if exitErr, ok := err.(*exec.ExitError); ok {
				if status, ok := exitErr.Sys().(syscall.WaitStatus); ok {
					if status.Signaled() && status.Signal() == syscall.SIGTERM {
						// Process was terminated by our SIGTERM, this is success
						return nil
					}
				}
			}
		}
		return err

	case <-time.After(gracePeriod):
		// Grace period expired, force kill and clean up container
		if p.config.Logger != nil {
			p.config.Logger.Warn("Container process grace period expired, forcing kill and cleanup",
				"gracePeriod", gracePeriod)
		}

		// Send SIGKILL
		if err := p.Signal(syscall.SIGKILL); err != nil {
			if p.config.Logger != nil {
				p.config.Logger.Warn("Failed to send SIGKILL", "error", err)
			}
		}

		// Clean up orphaned container
		p.cleanupContainer()

		// Wait for process to exit after SIGKILL
		select {
		case err := <-exitCh:
			if p.config.Logger != nil {
				p.config.Logger.Info("Container process killed after grace period")
			}

			// Clean up TTY resources
			if p.tty != nil {
				if closeErr := p.tty.Close(); closeErr != nil && err == nil {
					err = closeErr
				}
			}

			if err != nil {
				return fmt.Errorf("container process killed after grace period: %w", err)
			}
			return fmt.Errorf("container process killed after grace period")

		case <-time.After(time.Second):
			if p.config.Logger != nil {
				p.config.Logger.Error("Container process failed to exit after SIGKILL")
			}

			// Clean up TTY resources anyway
			if p.tty != nil {
				p.tty.Close()
			}

			return fmt.Errorf("container process failed to exit after SIGKILL")
		}
	}
}

// Close cleans up resources without stopping the process
// This is useful when the process has already exited
func (p *Process) Close() error {
	if p.tty != nil {
		return p.tty.Close()
	}
	return nil
}

// ResolvePID converts a container PID to host PID by looking up processes in the container's PID namespace
func (p *Process) ResolvePID(containerPID int) (int, error) {
	// If we don't have a container, return the PID unchanged
	if p.containerID == "" || p.containerPID == 0 {
		return containerPID, nil
	}

	// Get the init PID from crun state
	cmd := exec.Command("crun", "state", p.containerID)
	output, err := cmd.Output()
	if err != nil {
		if p.config.Logger != nil {
			p.config.Logger.Warn("Failed to get container state", "containerID", p.containerID, "error", err)
		}
		// Fall back to using stored container PID
		return HostPID(containerPID, p.containerPID)
	}

	// Parse the JSON output to get the init PID
	var state struct {
		PID int `json:"pid"`
	}
	if err := json.Unmarshal(output, &state); err != nil {
		if p.config.Logger != nil {
			p.config.Logger.Warn("Failed to parse container state", "error", err)
		}
		// Fall back to using stored container PID
		return HostPID(containerPID, p.containerPID)
	}

	if state.PID == 0 {
		// No init PID, fall back to stored container PID
		return HostPID(containerPID, p.containerPID)
	}

	// Special case: PID 1 in container is the init PID
	if containerPID == 1 {
		return state.PID, nil
	}

	// Get the PID namespace of the init process
	nsPath := fmt.Sprintf("/proc/%d/ns/pid", state.PID)
	nsTarget, err := os.Readlink(nsPath)
	if err != nil {
		return 0, fmt.Errorf("failed to read init PID namespace: %w", err)
	}

	// Search all processes for ones in the same PID namespace
	procDir, err := os.Open("/proc")
	if err != nil {
		return 0, fmt.Errorf("failed to open /proc: %w", err)
	}
	defer procDir.Close()

	entries, err := procDir.Readdir(-1)
	if err != nil {
		return 0, fmt.Errorf("failed to read /proc: %w", err)
	}

	for _, entry := range entries {
		// Skip non-numeric entries
		if !entry.IsDir() {
			continue
		}
		hostPID, err := strconv.Atoi(entry.Name())
		if err != nil {
			continue
		}

		// Check if this process is in the same namespace
		pidNsPath := fmt.Sprintf("/proc/%d/ns/pid", hostPID)
		pidNsTarget, err := os.Readlink(pidNsPath)
		if err != nil {
			continue
		}

		if pidNsTarget != nsTarget {
			continue
		}

		// Read the NSpid field from status to get the container PID
		statusPath := fmt.Sprintf("/proc/%d/status", hostPID)
		statusData, err := os.ReadFile(statusPath)
		if err != nil {
			continue
		}

		lines := strings.Split(string(statusData), "\n")
		for _, line := range lines {
			if strings.HasPrefix(line, "NSpid:") {
				fields := strings.Fields(line)
				if len(fields) >= 3 {
					// NSpid format: "NSpid: <PID in root ns> <PID in container ns>"
					// The last field is the PID as seen in the innermost namespace
					innerPIDStr := fields[len(fields)-1]
					innerPID, err := strconv.Atoi(innerPIDStr)
					if err == nil && innerPID == containerPID {
						return hostPID, nil
					}
				}
				break
			}
		}
	}

	return 0, fmt.Errorf("container PID %d not found in namespace of init PID %d", containerPID, state.PID)
}

// NewProcessBuilder provides a fluent interface for building process configurations
type ProcessBuilder struct {
	config ProcessConfig
}

// NewProcessBuilder creates a new process builder
func NewProcessBuilder(command string, args ...string) *ProcessBuilder {
	return &ProcessBuilder{
		config: ProcessConfig{
			Config: supervisor.Config{
				Command: command,
				Args:    args,
			},
		},
	}
}

// WithEnv sets environment variables
func (pb *ProcessBuilder) WithEnv(env []string) *ProcessBuilder {
	pb.config.Env = env
	return pb
}

// WithDir sets the working directory
func (pb *ProcessBuilder) WithDir(dir string) *ProcessBuilder {
	pb.config.Dir = dir
	return pb
}

// WithGracePeriod sets the grace period for shutdown
func (pb *ProcessBuilder) WithGracePeriod(period time.Duration) *ProcessBuilder {
	pb.config.GracePeriod = period
	return pb
}

// WithTTYTimeout sets the TTY acquisition timeout
// Only used when containers are enabled system-wide
func (pb *ProcessBuilder) WithTTYTimeout(timeout time.Duration) *ProcessBuilder {
	pb.config.TTYTimeout = timeout
	return pb
}

// WithTTYOutput sets where to forward TTY output
// Commonly set to os.Stdout to forward container output to logs
func (pb *ProcessBuilder) WithTTYOutput(output io.Writer) *ProcessBuilder {
	pb.config.TTYOutput = output
	return pb
}

// Build creates the Process instance
func (pb *ProcessBuilder) Build() (*Process, error) {
	return NewProcess(pb.config)
}
