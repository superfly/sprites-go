package container

import (
	"fmt"
	"io"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"syscall"
	"time"

	"github.com/superfly/sprite-env/packages/supervisor"
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
	containerPID int    // PID of the actual container process (not the crun wrapper)
	containerID  string // ID of the container for cleanup operations
}

// NewProcess creates a new process with automatic container support based on system config
func NewProcess(config ProcessConfig) (*Process, error) {
	var tty *Tty

	// Check if containers are enabled system-wide
	if IsEnabled() {
		// Generate a unique socket path in the configured directory
		socketPath := fmt.Sprintf("%s/container-process-%d-%d.sock",
			GetSocketDir(), os.Getpid(), time.Now().UnixNano())

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

	// Extract container ID from command if this is a container process
	var containerID string
	if tty != nil {
		containerID = extractContainerID(config.Command, config.Args)

		// Add CONTAINER_WRAPPED env var only for actual container processes
		if containerID != "" && isContainerCommand(config.Command, config.Args) {
			config.Env = append(config.Env, "CONTAINER_WRAPPED=true")
		}
	}

	return &Process{
		Supervisor:  supervisor,
		tty:         tty,
		config:      config,
		containerID: containerID,
	}, nil
}

// isContainerCommand checks if a command is running a container
func isContainerCommand(command string, args []string) bool {
	// Check if the command looks like a container runtime
	if strings.Contains(command, "crun") || strings.Contains(command, "runc") {
		return true
	}

	// Check if the command is the exec.sh script
	if strings.Contains(command, "exec.sh") || strings.Contains(command, "/exec.sh") {
		return true
	}

	return false
}

// extractContainerID attempts to extract the container ID from command and args
func extractContainerID(command string, args []string) string {
	// For base-env/exec.sh, the container ID is hardcoded as "app"
	if strings.Contains(command, "exec.sh") || strings.Contains(command, "/exec.sh") {
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

	// Default fallback for container commands
	if isContainerCommand(command, args) {
		return "app"
	}

	return ""
}

// Start starts the process and returns its PID
func (p *Process) Start() (int, error) {
	// Start the process using supervisor
	pid, err := p.Supervisor.Start()
	if err != nil {
		return -1, err
	}

	// Start TTY forwarding if configured and containers are enabled
	if p.config.TTYOutput != nil && p.tty != nil {
		go p.forwardTTY()
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

// cleanupContainer runs crun delete -f to clean up orphaned containers
func (p *Process) cleanupContainer() {
	if p.containerID == "" || !p.isContainerProcess() {
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
	pty, err := p.GetTTY()
	if err != nil {
		// TTY forwarding failed, but don't crash the process
		return
	}
	defer pty.Close()

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

	pty, err := p.tty.GetWithTimeout(timeout)
	if err != nil {
		return nil, err
	}

	// If this is a container process and we don't have the container PID yet,
	// discover it now that the container is running and connected
	if p.isContainerProcess() && p.containerPID == 0 {
		if p.config.Logger != nil {
			p.config.Logger.Debug("Container process detected, attempting to find container PID",
				"isContainer", p.isContainerProcess(),
				"currentContainerPID", p.containerPID)
		}
		p.findContainerProcess()
	} else if p.config.Logger != nil {
		p.config.Logger.Debug("Skipping container PID discovery",
			"isContainer", p.isContainerProcess(),
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

// Stop gracefully stops the process and cleans up resources
func (p *Process) Stop() error {
	// For container processes, implement custom graceful shutdown with container cleanup
	if p.isContainerProcess() {
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

// isContainerProcess checks if this process appears to be running a container
func (p *Process) isContainerProcess() bool {
	// Use the shared container command detection logic
	if isContainerCommand(p.config.Command, p.config.Args) {
		return true
	}

	// Check if CONTAINER_WRAPPED environment variable is set
	for _, env := range p.config.Env {
		if strings.HasPrefix(env, "CONTAINER_WRAPPED=") {
			return strings.HasSuffix(env, "=true")
		}
	}

	return false
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
