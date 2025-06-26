package container

import (
	"fmt"
	"io"
	"os"
	"time"

	"github.com/sprite-env/packages/supervisor"
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
	tty    *Tty
	config ProcessConfig
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

		// Add container runtime hint
		config.Env = append(config.Env, "CONTAINER_WRAPPED=true")

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

	return &Process{
		Supervisor: supervisor,
		tty:        tty,
		config:     config,
	}, nil
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

	return p.tty.GetWithTimeout(timeout)
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
	// Stop the supervisor first
	err := p.Supervisor.Stop()

	// Clean up TTY resources
	if p.tty != nil {
		if closeErr := p.tty.Close(); closeErr != nil && err == nil {
			err = closeErr
		}
	}

	return err
}

// Close cleans up resources without stopping the process
// This is useful when the process has already exited
func (p *Process) Close() error {
	if p.tty != nil {
		return p.tty.Close()
	}
	return nil
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
