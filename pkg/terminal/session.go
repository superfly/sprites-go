//go:build !clientonly
// +build !clientonly

// Package terminal provides a reusable library for interactive and non-interactive
// command execution with PTY support and transcript recording.
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

	// Transcript recording
	transcript TranscriptCollector

	// Logging
	logger *slog.Logger

	// Process start callback
	onProcessStart func(pid int)

	// PTY management for resize handling
	ptyFile *os.File // Current PTY file for resize operations
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

// WithTranscript sets the transcript collector for recording session I/O.
func WithTranscript(collector TranscriptCollector) Option {
	return func(s *Session) {
		s.transcript = collector
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
	transcript := s.transcript
	if transcript == nil {
		transcript = &NoopTranscript{}
	}
	defer transcript.Close()

	cmd, err := s.buildCommand(ctx)
	if err != nil {
		return -1, fmt.Errorf("failed to build command: %w", err)
	}

	if s.tty {
		return s.runWithTTY(ctx, cmd, stdin, stdout, transcript)
	}
	return s.runWithoutTTY(ctx, cmd, stdin, stdout, stderr, transcript)
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
			execEnv := strings.Join(s.env, "\n")
			cmd.Env = append(cmd.Env, fmt.Sprintf("EXEC_ENV=%s", execEnv))
			if s.logger != nil {
				s.logger.Debug("Passing environment variables to wrapper via EXEC_ENV", "env", s.env)
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
func (s *Session) runWithTTY(ctx context.Context, cmd *exec.Cmd, stdin io.Reader, stdout io.Writer, transcript TranscriptCollector) (int, error) {
	// Use console socket if specified, otherwise create a new PTY
	if s.consoleSocket != "" {
		return s.runWithConsoleSocket(ctx, cmd, stdin, stdout, transcript)
	}
	return s.runWithNewPTY(ctx, cmd, stdin, stdout, transcript)
}

// runWithNewPTY runs the command with a newly allocated PTY.
func (s *Session) runWithNewPTY(ctx context.Context, cmd *exec.Cmd, stdin io.Reader, stdout io.Writer, transcript TranscriptCollector) (int, error) {
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
	ioWg := s.startPTYIO(ctx, ptmx, stdin, stdout, transcript)

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
func (s *Session) runWithConsoleSocket(ctx context.Context, cmd *exec.Cmd, stdin io.Reader, stdout io.Writer, transcript TranscriptCollector) (int, error) {
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

	s.handlePTYIO(ctx, ptyFile, stdin, stdout, transcript)
	cmdErr := cmd.Wait()
	return getExitCode(cmdErr), nil
}

// runWithoutTTY executes the command without PTY, using separate streams.
func (s *Session) runWithoutTTY(ctx context.Context, cmd *exec.Cmd, stdin io.Reader, stdout, stderr io.Writer, transcript TranscriptCollector) (int, error) {
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
		teeReader := io.TeeReader(stdin, transcript.StreamWriter("stdin"))
		io.Copy(stdinPipe, teeReader)
	}()

	// Stream stdout to destination
	go func() {
		defer close(stdoutDone)
		multiWriter := io.MultiWriter(stdout, transcript.StreamWriter("stdout"))
		io.Copy(multiWriter, stdoutReader)
	}()

	// Stream stderr to destination
	go func() {
		defer close(stderrDone)
		multiWriter := io.MultiWriter(stderr, transcript.StreamWriter("stderr"))
		io.Copy(multiWriter, stderrReader)
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
func (s *Session) startPTYIO(ctx context.Context, pty *os.File, stdin io.Reader, stdout io.Writer, transcript TranscriptCollector) *sync.WaitGroup {
	inLog := transcript.StreamWriter("stdin")
	outLog := transcript.StreamWriter("stdout")

	var wg sync.WaitGroup

	// Handle stdin -> PTY
	go func() {
		teeReader := io.TeeReader(stdin, inLog)
		io.Copy(pty, teeReader)
		// This will exit when stdin is closed or PTY write fails
	}()

	// Handle PTY -> stdout
	wg.Add(1)
	go func() {
		defer wg.Done()
		multiWriter := io.MultiWriter(stdout, outLog)
		io.Copy(multiWriter, pty)
		// This will exit when PTY is closed (EOF)
	}()

	return &wg
}

// handlePTYIO manages I/O between the PTY and the provided streams.
// This is now deprecated in favor of startPTYIO but kept for console socket compatibility.
func (s *Session) handlePTYIO(ctx context.Context, pty *os.File, stdin io.Reader, stdout io.Writer, transcript TranscriptCollector) {
	wg := s.startPTYIO(ctx, pty, stdin, stdout, transcript)
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
