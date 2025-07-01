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

	creackpty "github.com/creack/pty"
	"github.com/superfly/sprite-env/packages/container"
)

// Session represents a terminal session configuration and execution environment.
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

	if len(s.env) > 0 {
		cmd.Env = append(cmd.Environ(), s.env...)
	}

	if len(s.wrapperCommand) > 0 {
		if cmd.Env == nil {
			cmd.Env = os.Environ()
		}

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
			if cmd.Env == nil {
				cmd.Env = os.Environ()
			}
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
	// Ensure TERM is set for PTY mode
	if cmd.Env == nil {
		cmd.Env = os.Environ()
	}
	termSet := false
	for _, env := range cmd.Env {
		if strings.HasPrefix(env, "TERM=") {
			termSet = true
			break
		}
	}
	if !termSet {
		cmd.Env = append(cmd.Env, "TERM=xterm")
	}

	if s.logger != nil {
		s.logger.Debug("Starting command with PTY", "cmd", cmd.Args)
	}

	ptmx, err := creackpty.Start(cmd)
	if err != nil {
		if s.logger != nil {
			s.logger.Error("Failed to start with PTY", "error", err)
		}
		return -1, fmt.Errorf("failed to start with PTY: %w", err)
	}
	defer ptmx.Close()

	// Set initial terminal size if specified
	if s.initialCols > 0 && s.initialRows > 0 {
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

	s.handlePTYIO(ctx, ptmx, stdin, stdout, transcript)
	cmdErr := cmd.Wait()
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

	if cmd.Env == nil {
		cmd.Env = os.Environ()
	}
	cmd.Env = append(cmd.Env, "TERM=xterm")
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

	if s.initialCols > 0 && s.initialRows > 0 {
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

	s.handlePTYIO(ctx, ptyFile, stdin, stdout, transcript)
	cmdErr := cmd.Wait()
	return getExitCode(cmdErr), nil
}

// runWithoutTTY executes the command without PTY, using separate streams.
func (s *Session) runWithoutTTY(ctx context.Context, cmd *exec.Cmd, stdin io.Reader, stdout, stderr io.Writer, transcript TranscriptCollector) (int, error) {
	stdinPipe, err := cmd.StdinPipe()
	if err != nil {
		return -1, fmt.Errorf("failed to create stdin pipe: %w", err)
	}
	stdoutPipe, err := cmd.StdoutPipe()
	if err != nil {
		return -1, fmt.Errorf("failed to create stdout pipe: %w", err)
	}
	stderrPipe, err := cmd.StderrPipe()
	if err != nil {
		return -1, fmt.Errorf("failed to create stderr pipe: %w", err)
	}

	if err := cmd.Start(); err != nil {
		return -1, fmt.Errorf("failed to start command: %w", err)
	}

	done := make(chan struct{})

	// Stdin: copy from input to command
	go func() {
		defer stdinPipe.Close()
		teeReader := io.TeeReader(stdin, transcript.StreamWriter("stdin"))
		io.Copy(stdinPipe, teeReader)
	}()

	// Stdout: copy from command to output
	go func() {
		defer func() { done <- struct{}{} }()
		multiWriter := io.MultiWriter(stdout, transcript.StreamWriter("stdout"))
		io.Copy(multiWriter, stdoutPipe)
	}()

	// Stderr: copy from command to output
	go func() {
		defer func() { done <- struct{}{} }()
		multiWriter := io.MultiWriter(stderr, transcript.StreamWriter("stderr"))
		io.Copy(multiWriter, stderrPipe)
	}()

	go func() {
		<-done // stdout done
		<-done // stderr done
		close(done)
	}()

	cmdErr := cmd.Wait()

	select {
	case <-done:
	case <-ctx.Done():
	}

	return getExitCode(cmdErr), nil
}

// handlePTYIO manages I/O between the PTY and the provided streams.
func (s *Session) handlePTYIO(ctx context.Context, pty *os.File, stdin io.Reader, stdout io.Writer, transcript TranscriptCollector) {
	inLog := transcript.StreamWriter("stdin")
	outLog := transcript.StreamWriter("stdout")

	stdinDone := make(chan struct{})
	stdoutDone := make(chan struct{})

	// Handle stdin -> PTY
	go func() {
		defer close(stdinDone)
		teeReader := io.TeeReader(stdin, inLog)
		io.Copy(pty, teeReader)
	}()

	// Handle PTY -> stdout
	go func() {
		defer close(stdoutDone)
		multiWriter := io.MultiWriter(stdout, outLog)
		io.Copy(multiWriter, pty)
	}()

	select {
	case <-stdinDone:
	case <-stdoutDone:
	case <-ctx.Done():
	}
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
