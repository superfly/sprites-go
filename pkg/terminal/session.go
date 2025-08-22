//go:build !clientonly
// +build !clientonly

// Package terminal provides a reusable library for interactive and non-interactive
// command execution with PTY support.
package terminal

import (
	"context"
	"fmt"
	"io"
	"log/slog"
	"os"
	"os/exec"
	"strings"
	"sync"
	"syscall"
	"time"

	creackpty "github.com/creack/pty"
	"github.com/superfly/sprite-env/packages/container"
)

// Session represents a terminal session that can execute commands.
type Session struct {
	// Command configuration
	path string
	args []string
	env  []string
	dir  string

	// Terminal configuration
	tty           bool
	initialCols   uint16
	initialRows   uint16
	consoleSocket string

	// Wrapper command (e.g., exec.sh)
	wrapperCommand []string

	// Logging
	logger *slog.Logger

	// Process start callback
	onProcessStart func(pid int)

	// PTY management for resize handling
	ptyFile *os.File // Current PTY file for resize operations

	// Process tracking
	processPID int        // PID of the started process
	mu         sync.Mutex // Protects processPID
}

// Option represents a configuration option for a Session.
type Option func(*Session)

// NewSession creates a new terminal session with the given options.
func NewSession(options ...Option) *Session {
	s := &Session{
		path: "bash",
		args: []string{"bash", "-l"},
	}

	for _, opt := range options {
		opt(s)
	}

	return s
}

// WithCommand sets the command path and arguments.
func WithCommand(path string, args ...string) Option {
	return func(s *Session) {
		s.path = path
		s.args = append([]string{path}, args...)
	}
}

// WithTTY enables or disables TTY mode.
func WithTTY(enabled bool) Option {
	return func(s *Session) {
		s.tty = enabled
	}
}

// WithEnv sets environment variables for the command.
func WithEnv(env []string) Option {
	return func(s *Session) {
		s.env = env
	}
}

// WithDir sets the working directory for the command.
func WithDir(workingDir string) Option {
	return func(s *Session) {
		s.dir = workingDir
	}
}

// WithWrapper sets a wrapper command to execute before the main command.
func WithWrapper(wrapper []string) Option {
	return func(s *Session) {
		s.wrapperCommand = wrapper
	}
}

// WithTerminalSize sets the initial terminal size for TTY mode.
func WithTerminalSize(cols, rows uint16) Option {
	return func(s *Session) {
		s.initialCols = cols
		s.initialRows = rows
	}
}

// WithConsoleSocket sets the console socket path for crun integration.
func WithConsoleSocket(path string) Option {
	return func(s *Session) {
		s.consoleSocket = path
	}
}

// WithLogger sets the logger for the session.
func WithLogger(logger *slog.Logger) Option {
	return func(s *Session) {
		s.logger = logger
	}
}

// WithOnProcessStart sets a callback to be called when the process starts with its PID.
func WithOnProcessStart(callback func(pid int)) Option {
	return func(s *Session) {
		s.onProcessStart = callback
	}
}

// Resize resizes the terminal to the specified dimensions.
// This method is thread-safe and can be called from WebSocket handlers.
func (s *Session) Resize(cols, rows uint16) error {
	if !s.tty || s.ptyFile == nil {
		return nil // Ignore resize for non-TTY sessions or when PTY is not available
	}

	// Try to get current PTY size for comparison
	var currentCols, currentRows uint16
	if currentSize, err := creackpty.GetsizeFull(s.ptyFile); err == nil {
		currentCols = currentSize.Cols
		currentRows = currentSize.Rows
	}

	if s.logger != nil {
		s.logger.Debug("Resizing terminal PTY",
			"newCols", cols,
			"newRows", rows,
			"currentCols", currentCols,
			"currentRows", currentRows)
	}

	if err := creackpty.Setsize(s.ptyFile, &creackpty.Winsize{
		Cols: cols,
		Rows: rows,
	}); err != nil {
		if s.logger != nil {
			s.logger.Warn("Failed to resize terminal PTY", "error", err)
		}
		return err
	}

	if s.logger != nil {
		s.logger.Debug("Terminal PTY resized successfully - SIGWINCH should be sent to foreground process group", "cols", cols, "rows", rows)
	}

	return nil
}

// Run executes the configured command with the given I/O streams.
// Returns the exit code and any error that occurred during execution.
func (s *Session) Run(ctx context.Context, stdin io.Reader, stdout, stderr io.Writer) (int, error) {
	cmd, err := s.buildCommand(ctx)
	if err != nil {
		return -1, fmt.Errorf("failed to build command: %w", err)
	}

	if s.tty {
		return s.runWithTTY(ctx, cmd, stdin, stdout)
	}
	return s.runWithoutTTY(ctx, cmd, stdin, stdout, stderr)
}

// buildCommand creates the exec.Cmd with proper configuration.
func (s *Session) buildCommand(ctx context.Context) (*exec.Cmd, error) {
	var cmdArgs []string
	if len(s.wrapperCommand) > 0 {
		cmdArgs = append(cmdArgs, s.wrapperCommand...)
		cmdArgs = append(cmdArgs, s.args...)
	} else {
		cmdArgs = s.args
	}

	if len(cmdArgs) == 0 {
		cmdArgs = []string{s.path}
	}

	cmd := exec.CommandContext(ctx, cmdArgs[0], cmdArgs[1:]...)

	// Start with environment from system
	cmd.Env = os.Environ()

	// Apply user-provided environment variables, which will override system ones
	if len(s.env) > 0 {
		cmd.Env = append(cmd.Env, s.env...)
	}

	if len(s.wrapperCommand) > 0 {
		if len(s.env) > 0 {
			// Pass each environment variable individually with a prefix
			for _, envVar := range s.env {
				// Extract the variable name (everything before the first =)
				if idx := strings.Index(envVar, "="); idx > 0 {
					varName := envVar[:idx]
					cmd.Env = append(cmd.Env, fmt.Sprintf("EXEC_ENV_%s=%s", varName, envVar))
				}
			}
			if s.logger != nil {
				s.logger.Debug("Passing environment variables to wrapper individually", "env", s.env)
			}
		}
	}

	if s.dir != "" {
		if len(s.wrapperCommand) > 0 {
			// When using a wrapper command, pass the directory as an environment variable
			cmd.Env = append(cmd.Env, fmt.Sprintf("EXEC_DIR=%s", s.dir))
			if s.logger != nil {
				s.logger.Debug("Passing working directory to wrapper via EXEC_DIR", "dir", s.dir)
			}
		} else {
			// No wrapper command, set the directory directly
			cmd.Dir = s.dir
			if s.logger != nil {
				s.logger.Debug("Setting working directory directly", "dir", s.dir)
			}
		}
	}

	return cmd, nil
}

// runWithTTY executes the command with PTY support.
func (s *Session) runWithTTY(ctx context.Context, cmd *exec.Cmd, stdin io.Reader, stdout io.Writer) (int, error) {
	// Use console socket if specified, otherwise create a new PTY
	if s.consoleSocket != "" {
		return s.runWithConsoleSocket(ctx, cmd, stdin, stdout)
	}
	return s.runWithNewPTY(ctx, cmd, stdin, stdout)
}

// runWithNewPTY runs the command with a newly allocated PTY.
func (s *Session) runWithNewPTY(ctx context.Context, cmd *exec.Cmd, stdin io.Reader, stdout io.Writer) (int, error) {
	// Ensure TERM is set for PTY mode (only if not already set)
	termSet := false
	colorTermSet := false
	for _, env := range cmd.Env {
		if strings.HasPrefix(env, "TERM=") {
			termSet = true
		}
		if strings.HasPrefix(env, "COLORTERM=") {
			colorTermSet = true
		}
	}
	if !termSet {
		// Default to xterm-256color for better compatibility
		cmd.Env = append(cmd.Env, "TERM=xterm-256color")
		if s.logger != nil {
			s.logger.Debug("No TERM set, defaulting to xterm-256color")
		}
	}
	// Also ensure COLORTERM is set for better color support
	if !colorTermSet {
		cmd.Env = append(cmd.Env, "COLORTERM=truecolor")
	}

	if s.logger != nil {
		s.logger.Debug("Starting command with PTY", "cmd", cmd.Args, "env", cmd.Env)
	}

	// Open PTY manually to set up I/O before starting command
	ptmx, tty, err := creackpty.Open()
	if err != nil {
		if s.logger != nil {
			s.logger.Error("Failed to open PTY", "error", err)
		}
		return -1, fmt.Errorf("failed to open PTY: %w", err)
	}
	defer ptmx.Close()
	defer tty.Close()

	// Store PTY reference for resize operations
	s.ptyFile = ptmx

	// Apply initial terminal size if specified
	if s.initialCols > 0 && s.initialRows > 0 {
		// Try to get current PTY size for comparison
		var currentCols, currentRows uint16
		if currentSize, err := creackpty.GetsizeFull(ptmx); err == nil {
			currentCols = currentSize.Cols
			currentRows = currentSize.Rows
		}

		if s.logger != nil {
			s.logger.Info("Setting initial PTY size (before command start)",
				"cols", s.initialCols,
				"rows", s.initialRows,
				"currentCols", currentCols,
				"currentRows", currentRows,
				"location", "runWithTTY:beforeStart")
		}
		if err := creackpty.Setsize(ptmx, &creackpty.Winsize{
			Cols: s.initialCols,
			Rows: s.initialRows,
		}); err != nil {
			if s.logger != nil {
				s.logger.Warn("Failed to set initial PTY size", "error", err)
			}
		} else if s.logger != nil {
			s.logger.Debug("Set initial PTY size", "cols", s.initialCols, "rows", s.initialRows)
		}
	}

	// Assign TTY to command stdio
	cmd.Stdin = tty
	cmd.Stdout = tty
	cmd.Stderr = tty

	// Start with special handling for controlling TTY
	if cmd.SysProcAttr == nil {
		cmd.SysProcAttr = &syscall.SysProcAttr{}
	}
	cmd.SysProcAttr.Setsid = true
	cmd.SysProcAttr.Setctty = true

	// Start PTY I/O handling BEFORE starting the command
	// This ensures we're ready to receive output immediately
	ioWg := s.startPTYIO(ctx, ptmx, stdin, stdout)

	// Now start the command
	if err := cmd.Start(); err != nil {
		if s.logger != nil {
			s.logger.Error("Failed to start command", "error", err)
		}
		return -1, fmt.Errorf("failed to start command: %w", err)
	}

	// Close the TTY file descriptor in parent process after starting child
	tty.Close()

	// Call process start callback if provided
	if s.onProcessStart != nil && cmd.Process != nil {
		s.onProcessStart(cmd.Process.Pid)
		if s.logger != nil {
			s.logger.Debug("Terminal session process started with PTY", "pid", cmd.Process.Pid)
		}
	}

	// Track the process PID
	s.mu.Lock()
	s.processPID = cmd.Process.Pid
	s.mu.Unlock()

	// Set initial terminal size if specified
	if s.initialCols > 0 && s.initialRows > 0 {
		// Try to get current PTY size for comparison
		var currentCols, currentRows uint16
		if currentSize, err := creackpty.GetsizeFull(ptmx); err == nil {
			currentCols = currentSize.Cols
			currentRows = currentSize.Rows
		}

		if s.logger != nil {
			s.logger.Info("Setting initial PTY size (after command start)",
				"cols", s.initialCols,
				"rows", s.initialRows,
				"currentCols", currentCols,
				"currentRows", currentRows,
				"location", "runWithTTY:afterStart",
				"pid", cmd.Process.Pid)
		}
		if err := creackpty.Setsize(ptmx, &creackpty.Winsize{
			Cols: s.initialCols,
			Rows: s.initialRows,
		}); err != nil {
			if s.logger != nil {
				s.logger.Warn("Failed to set initial PTY size", "error", err)
			}
		} else if s.logger != nil {
			s.logger.Debug("Set initial PTY size", "cols", s.initialCols, "rows", s.initialRows)
		}
	}

	// Wait for command to complete
	cmdErr := cmd.Wait()

	// Process has exited, PTY slave is closed.
	// Wait for I/O to complete (goroutines will get EOF from PTY).
	ioWg.Wait()

	// All I/O is complete, now close the PTY master
	// (already closed by defer, but being explicit about order)

	return getExitCode(cmdErr), nil
}

// runWithConsoleSocket runs the command using crun's console socket.
func (s *Session) runWithConsoleSocket(ctx context.Context, cmd *exec.Cmd, stdin io.Reader, stdout io.Writer) (int, error) {
	tty, err := container.NewWithPath(s.consoleSocket)
	if err != nil {
		if s.logger != nil {
			s.logger.Error("Failed to create TTY manager", "error", err)
		}
		return -1, fmt.Errorf("failed to create TTY manager: %w", err)
	}
	defer tty.Close()

	// Ensure TERM is set for PTY mode (only if not already set)
	termSet := false
	for _, env := range cmd.Env {
		if strings.HasPrefix(env, "TERM=") {
			termSet = true
			break
		}
	}
	if !termSet {
		// Default to xterm-256color for better compatibility
		cmd.Env = append(cmd.Env, "TERM=xterm-256color")
		if s.logger != nil {
			s.logger.Debug("No TERM set, defaulting to xterm-256color")
		}
	}

	cmd.Env = append(cmd.Env, fmt.Sprintf("CONSOLE_SOCKET=%s", s.consoleSocket))

	// Clear standard streams - crun will create them
	cmd.Stdin = nil
	cmd.Stdout = nil
	cmd.Stderr = nil

	if s.logger != nil {
		s.logger.Debug("Starting command with console-socket", "cmd", cmd.Args, "socket", s.consoleSocket)
	}

	if err := cmd.Start(); err != nil {
		if s.logger != nil {
			s.logger.Error("Failed to start command", "error", err)
		}
		return -1, fmt.Errorf("failed to start command: %w", err)
	}

	// Call process start callback with the wrapper PID
	// PID unwrapping is now handled by the port watcher itself
	if s.onProcessStart != nil {
		s.onProcessStart(cmd.Process.Pid)
		if s.logger != nil {
			s.logger.Debug("Terminal session process started with console socket",
				"pid", cmd.Process.Pid)
		}
	}

	// Track the process PID
	s.mu.Lock()
	s.processPID = cmd.Process.Pid
	s.mu.Unlock()

	// Wait for crun to send us the PTY
	ptyFile, err := tty.Get()
	if err != nil {
		if s.logger != nil {
			s.logger.Error("Failed to receive PTY from console socket", "error", err)
		}
		cmd.Process.Kill()
		cmd.Wait()
		return -1, fmt.Errorf("failed to receive PTY: %w", err)
	}
	defer ptyFile.Close()

	if s.logger != nil {
		s.logger.Debug("Received PTY from console socket")
	}

	// Store PTY reference for resize operations
	s.ptyFile = ptyFile

	if s.initialCols > 0 && s.initialRows > 0 {
		// Try to get current PTY size for comparison
		var currentCols, currentRows uint16
		if currentSize, err := creackpty.GetsizeFull(ptyFile); err == nil {
			currentCols = currentSize.Cols
			currentRows = currentSize.Rows
		}

		if s.logger != nil {
			s.logger.Info("Setting initial PTY size (console socket mode)",
				"cols", s.initialCols,
				"rows", s.initialRows,
				"currentCols", currentCols,
				"currentRows", currentRows,
				"location", "runWithConsoleSocket",
				"pid", cmd.Process.Pid)
		}
		if err := creackpty.Setsize(ptyFile, &creackpty.Winsize{
			Cols: s.initialCols,
			Rows: s.initialRows,
		}); err != nil {
			if s.logger != nil {
				s.logger.Warn("Failed to set initial PTY size", "error", err)
			}
		} else if s.logger != nil {
			s.logger.Debug("Set initial PTY size", "cols", s.initialCols, "rows", s.initialRows)
		}
	}

	// Disable local echo on the PTY to prevent duplicate characters
	// The client terminal is already in raw mode and handling echo
	if err := disablePTYEcho(ptyFile); err != nil {
		if s.logger != nil {
			s.logger.Warn("Failed to disable PTY echo", "error", err)
		}
		// Continue anyway - PTY will work but might have echo issues
	}

	s.handlePTYIO(ctx, ptyFile, stdin, stdout)
	cmdErr := cmd.Wait()
	return getExitCode(cmdErr), nil
}

// runWithoutTTY executes the command without PTY, using separate streams.
func (s *Session) runWithoutTTY(ctx context.Context, cmd *exec.Cmd, stdin io.Reader, stdout, stderr io.Writer) (int, error) {
	// Set up process group for non-TTY sessions
	// This ensures child processes are killed when the parent is killed
	if cmd.SysProcAttr == nil {
		cmd.SysProcAttr = &syscall.SysProcAttr{}
	}
	cmd.SysProcAttr.Setpgid = true

	// Use io.Pipe to let exec manage the goroutines
	stdoutReader, stdoutWriter := io.Pipe()
	stderrReader, stderrWriter := io.Pipe()

	// Assign writers to cmd
	cmd.Stdout = stdoutWriter
	cmd.Stderr = stderrWriter

	// Set up stdin pipe
	stdinPipe, err := cmd.StdinPipe()
	if err != nil {
		return -1, fmt.Errorf("failed to create stdin pipe: %w", err)
	}

	// Start I/O goroutines
	stdoutDone := make(chan struct{})
	stderrDone := make(chan struct{})

	// Copy stdin to the process
	go func() {
		defer stdinPipe.Close()
		io.Copy(stdinPipe, stdin)
	}()

	// Stream stdout to destination
	go func() {
		defer close(stdoutDone)
		io.Copy(stdout, stdoutReader)
	}()

	// Stream stderr to destination
	go func() {
		defer close(stderrDone)
		io.Copy(stderr, stderrReader)
	}()

	// Start the command
	if err := cmd.Start(); err != nil {
		stdoutWriter.Close()
		stderrWriter.Close()
		return -1, fmt.Errorf("failed to start command: %w", err)
	}

	// Call process start callback if provided
	if s.onProcessStart != nil && cmd.Process != nil {
		s.onProcessStart(cmd.Process.Pid)
		if s.logger != nil {
			s.logger.Debug("Terminal session process started without TTY", "pid", cmd.Process.Pid)
		}
	}

	// Track the process PID
	s.mu.Lock()
	s.processPID = cmd.Process.Pid
	s.mu.Unlock()

	// Wait for command to complete
	cmdErr := cmd.Wait()

	// Close writers to signal EOF
	stdoutWriter.Close()
	stderrWriter.Close()

	// Wait for readers to finish
	<-stdoutDone
	<-stderrDone

	return getExitCode(cmdErr), nil
}

// startPTYIO starts I/O goroutines for PTY handling and returns a WaitGroup.
// The caller should wait on the WaitGroup after the process exits to ensure
// all data has been read before closing the PTY.
func (s *Session) startPTYIO(ctx context.Context, pty *os.File, stdin io.Reader, stdout io.Writer) *sync.WaitGroup {
	var wg sync.WaitGroup

	// Handle stdin -> PTY
	go func() {
		io.Copy(pty, stdin)
		// This will exit when stdin is closed or PTY write fails
	}()

	// Handle PTY -> stdout
	wg.Add(1)
	go func() {
		defer wg.Done()
		io.Copy(stdout, pty)
		// This will exit when PTY is closed (EOF)
	}()

	return &wg
}

// handlePTYIO manages I/O between the PTY and the provided streams.
// This is now deprecated in favor of startPTYIO but kept for console socket compatibility.
func (s *Session) handlePTYIO(ctx context.Context, pty *os.File, stdin io.Reader, stdout io.Writer) {
	wg := s.startPTYIO(ctx, pty, stdin, stdout)
	wg.Wait()
}

// getExitCode extracts the exit code from a command error.
func getExitCode(err error) int {
	if err == nil {
		return 0
	}
	if exitErr, ok := err.(*exec.ExitError); ok {
		return exitErr.ExitCode()
	}
	return -1
}

// isContainerCommand checks if this session is running a container command
func (s *Session) isContainerCommand() bool {
	// Any command with a wrapper could spawn child processes that need tracking
	return len(s.wrapperCommand) > 0
}

// killContainerProcess kills the container process if this is a container command
func (s *Session) killContainerProcess() error {
	s.mu.Lock()
	processPID := s.processPID
	s.mu.Unlock()

	if processPID <= 0 {
		return nil
	}

	// Only check for container process if this is a container command
	if !s.isContainerCommand() {
		return nil
	}

	// Get the actual container PID from the container package
	containerPID, err := container.GetContainerPID(processPID)
	if err != nil {
		if s.logger != nil {
			s.logger.Debug("Failed to get container PID, process may have already exited",
				"wrapperPID", processPID,
				"error", err)
		}
		return nil
	}

	if s.logger != nil {
		s.logger.Debug("Attempting to kill container process",
			"wrapperPID", processPID,
			"containerPID", containerPID)
	}

	// For TTY sessions, try SIGHUP first (like SSH does when connection drops)
	if s.tty {
		if s.logger != nil {
			s.logger.Debug("Sending SIGHUP to container process (TTY session)",
				"containerPID", containerPID)
		}

		err := syscall.Kill(containerPID, syscall.SIGHUP)
		if err != nil {
			if s.logger != nil {
				s.logger.Debug("SIGHUP failed", "containerPID", containerPID, "error", err)
			}
		} else {
			// Give it a moment to handle SIGHUP
			time.Sleep(50 * time.Millisecond)

			// Check if it exited
			if err := syscall.Kill(containerPID, 0); err != nil {
				// Process is gone
				if s.logger != nil {
					s.logger.Debug("Container process exited after SIGHUP",
						"containerPID", containerPID)
				}
				return nil
			}
		}
	}

	// Try SIGTERM (or as fallback if SIGHUP didn't work)
	if s.logger != nil {
		s.logger.Debug("Sending SIGTERM to container process",
			"containerPID", containerPID)
	}

	err = syscall.Kill(containerPID, syscall.SIGTERM)
	if err != nil {
		if s.logger != nil {
			s.logger.Debug("SIGTERM failed", "containerPID", containerPID, "error", err)
		}
	} else {
		// Give it a moment to handle SIGTERM
		time.Sleep(100 * time.Millisecond)

		// Check if it's still alive
		if err := syscall.Kill(containerPID, 0); err != nil {
			// Process is gone
			if s.logger != nil {
				s.logger.Debug("Container process exited after SIGTERM",
					"containerPID", containerPID)
			}
			return nil
		}
	}

	// If still alive, force kill with SIGKILL
	if s.logger != nil {
		s.logger.Debug("Container process still alive, sending SIGKILL",
			"containerPID", containerPID)
	}

	err = syscall.Kill(containerPID, syscall.SIGKILL)
	if err != nil {
		if s.logger != nil {
			s.logger.Debug("SIGKILL failed", "containerPID", containerPID, "error", err)
		}
		return err
	}

	if s.logger != nil {
		s.logger.Debug("Sent SIGKILL to container process", "containerPID", containerPID)
	}

	return nil
}
