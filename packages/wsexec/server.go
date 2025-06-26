package wsexec

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"os"
	"os/exec"
	"strings"
	"sync"
	"time"

	creackpty "github.com/creack/pty"
	gorillaws "github.com/gorilla/websocket"
	"github.com/superfly/sprite-env/packages/container"
)

// configurePTY sets up the PTY for proper interactive use
func configurePTY(ptyFile *os.File) error {
	// PTY configuration is platform-specific and complex
	// For now, we'll rely on the programs running in the PTY to set their own modes
	// Most interactive programs (bash, vim, etc.) will configure the PTY as needed

	// TODO: In the future, we could use platform-specific build tags to implement
	// proper PTY configuration for each OS

	return nil
}

// NewServerCommandContext creates a new ServerCommand with context for executing a command
func NewServerCommandContext(ctx context.Context, name string, args ...string) *ServerCommand {
	cmd := &ServerCommand{
		Path: name,
		Args: append([]string{name}, args...),
		ctx:  ctx,
	}
	return cmd
}

// NewServerCommand creates a new ServerCommand for executing a command
func NewServerCommand(name string, args ...string) *ServerCommand {
	return NewServerCommandContext(context.Background(), name, args...)
}

// ServerCommand represents a command handler on the server side
type ServerCommand struct {
	// Command configuration
	Path string
	Args []string
	Env  []string
	Dir  string
	Tty  bool

	// Initial terminal size (for PTY mode)
	InitialCols uint16
	InitialRows uint16

	// Console socket path for receiving PTY from crun
	ConsoleSocketPath string
	LogPath           string

	// Wrapper commands (optional)
	WrapperCommand []string

	// Optional logger
	Logger *slog.Logger

	// Context for cancellation
	ctx context.Context
}

// SetTTY sets whether the command should run with a TTY
func (c *ServerCommand) SetTTY(tty bool) *ServerCommand {
	c.Tty = tty
	return c
}

// SetEnv sets the environment variables for the command
func (c *ServerCommand) SetEnv(env []string) *ServerCommand {
	c.Env = env
	return c
}

// SetWorkingDir sets the working directory for the command
func (c *ServerCommand) SetWorkingDir(dir string) *ServerCommand {
	c.Dir = dir
	return c
}

// SetWrapperCommand sets a wrapper command to execute before the main command
func (c *ServerCommand) SetWrapperCommand(wrapper []string) *ServerCommand {
	c.WrapperCommand = wrapper
	return c
}

// SetLogger sets the logger for the command
func (c *ServerCommand) SetLogger(logger *slog.Logger) *ServerCommand {
	c.Logger = logger
	return c
}

// SetContext sets the context for the command
func (c *ServerCommand) SetContext(ctx context.Context) *ServerCommand {
	c.ctx = ctx
	return c
}

// SetConsoleSocketPath sets the path for console socket to receive PTY from crun
func (c *ServerCommand) SetConsoleSocketPath(path string) *ServerCommand {
	c.ConsoleSocketPath = path
	return c
}

func (c *ServerCommand) SetLogPath(path string) *ServerCommand {
	c.LogPath = path
	return c
}

// SetInitialTerminalSize sets the initial terminal size for PTY mode
func (c *ServerCommand) SetInitialTerminalSize(cols, rows uint16) *ServerCommand {
	c.InitialCols = cols
	c.InitialRows = rows
	return c
}

// GetContext returns the context for the command
func (c *ServerCommand) GetContext() context.Context {
	if c.ctx == nil {
		return context.Background()
	}
	return c.ctx
}

// Handle upgrades the HTTP request to WebSocket and executes the command
func (c *ServerCommand) Handle(w http.ResponseWriter, r *http.Request) error {
	if c.Logger != nil {
		c.Logger.Debug("ServerCommand.Handle: Starting WebSocket upgrade",
			"url", r.URL.String(),
			"method", r.Method,
			"headers", r.Header)
	}

	// Set up WebSocket upgrader
	upgrader := gorillaws.Upgrader{
		ReadBufferSize:  1024 * 1024, // 1MB buffer
		WriteBufferSize: 1024 * 1024, // 1MB buffer
		CheckOrigin: func(r *http.Request) bool {
			if c.Logger != nil {
				c.Logger.Debug("ServerCommand.Handle: CheckOrigin called",
					"origin", r.Header.Get("Origin"),
					"host", r.Host)
			}
			// TODO: Add proper origin checking
			return true
		},
	}

	if c.Logger != nil {
		c.Logger.Debug("ServerCommand.Handle: Attempting WebSocket upgrade")
	}

	// Upgrade to WebSocket
	conn, err := upgrader.Upgrade(w, r, nil)
	if err != nil {
		if c.Logger != nil {
			c.Logger.Error("ServerCommand.Handle: WebSocket upgrade failed", "error", err)
		}
		return fmt.Errorf("failed to upgrade connection: %w", err)
	}
	defer conn.Close()

	// Set read limit to allow large messages (10MB)
	conn.SetReadLimit(10 * 1024 * 1024)

	if c.Logger != nil {
		c.Logger.Info("ServerCommand.Handle: WebSocket upgrade successful")
	}

	adapter := NewAdapter(conn, c.Tty)
	defer adapter.Close()

	// Run the command using the ServerCommand's context, fallback to request context
	ctx := c.GetContext()
	if ctx == context.Background() && r.Context() != context.Background() {
		ctx = r.Context()
	}

	if c.Logger != nil {
		c.Logger.Debug("ServerCommand.Handle: Starting command execution",
			"path", c.Path,
			"args", c.Args,
			"tty", c.Tty)
	}

	exitCode := c.run(ctx, adapter)

	if c.Logger != nil {
		c.Logger.Debug("ServerCommand.Handle: Command execution completed", "exitCode", exitCode)
	}

	// Give a moment for any remaining output to be sent
	// This is important for non-PTY mode where we have separate stdout/stderr streams
	time.Sleep(50 * time.Millisecond)

	// Send exit code
	if err := adapter.WriteExit(exitCode); err != nil {
		if c.Logger != nil {
			c.Logger.Error("ServerCommand.Handle: Failed to send exit code", "error", err)
		}
	}

	// Graceful close
	deadline := time.Now().Add(2 * time.Second)
	conn.WriteControl(gorillaws.CloseMessage,
		gorillaws.FormatCloseMessage(gorillaws.CloseNormalClosure, ""),
		deadline)

	// Wait for client close
	conn.SetReadDeadline(deadline)
	for {
		if _, _, err := conn.ReadMessage(); err != nil {
			break
		}
	}

	if c.Logger != nil {
		c.Logger.Debug("ServerCommand.Handle: WebSocket connection closed gracefully")
	}

	return nil
}

// run executes the command and handles I/O
func (c *ServerCommand) run(ctx context.Context, ws *Adapter) int {
	var (
		inLog, outLog, errLog *lineLogger
		logFile               *os.File
		err                   error
	)

	if c.LogPath != "" {
		logFile, err = os.OpenFile(c.LogPath,
			os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0644)
		if err == nil {
			logger := slog.New(slog.NewTextHandler(logFile, nil))
			inLog = newLogger("stdin", logger)
			outLog = newLogger("stdout", logger)
			errLog = newLogger("stderr", logger)
		}
	}
	defer func() {
		inLog.Close()
		outLog.Close()
		errLog.Close()
		logFile.Close()
	}()

	// Build command
	var cmdArgs []string
	if len(c.WrapperCommand) > 0 {
		cmdArgs = append(cmdArgs, c.WrapperCommand...)
		cmdArgs = append(cmdArgs, c.Args...)
	} else {
		cmdArgs = c.Args
	}

	if len(cmdArgs) == 0 {
		cmdArgs = []string{c.Path}
	}

	cmd := exec.CommandContext(ctx, cmdArgs[0], cmdArgs[1:]...)

	// Set environment
	if len(c.Env) > 0 {
		cmd.Env = append(cmd.Environ(), c.Env...)
	}

	// Handle wrapper-specific environment variables
	if len(c.WrapperCommand) > 0 {
		if cmd.Env == nil {
			cmd.Env = os.Environ()
		}

		// Pass environment variables to the wrapper script
		if len(c.Env) > 0 {
			// Join environment variables with newlines for the wrapper script
			execEnv := strings.Join(c.Env, "\n")
			cmd.Env = append(cmd.Env, fmt.Sprintf("EXEC_ENV=%s", execEnv))

			if c.Logger != nil {
				c.Logger.Debug("Passing environment variables to wrapper via EXEC_ENV", "env", c.Env)
			}
		}
	}

	// Handle working directory
	if c.Dir != "" {
		if len(c.WrapperCommand) > 0 {
			// When using a wrapper command, pass the directory as an environment variable
			// instead of setting cmd.Dir, so the wrapper can handle the directory change
			cmd.Env = append(cmd.Env, fmt.Sprintf("EXEC_DIR=%s", c.Dir))

			if c.Logger != nil {
				c.Logger.Debug("Passing working directory to wrapper via EXEC_DIR", "dir", c.Dir)
			}
		} else {
			// No wrapper command, set the directory directly
			cmd.Dir = c.Dir

			if c.Logger != nil {
				c.Logger.Debug("Setting working directory directly", "dir", c.Dir)
			}
		}
	}

	// Handle TTY mode
	if c.Tty {
		if c.ConsoleSocketPath != "" {
			return c.runWithConsoleSocket(ctx, cmd, ws, inLog, outLog)
		}
		return c.runWithNewPTY(ctx, cmd, ws, inLog, outLog)
	}
	return c.runWithoutPTY(ctx, cmd, ws, inLog, outLog, errLog)
}

// handlePTYIO handles the I/O between WebSocket and PTY
func (c *ServerCommand) handlePTYIO(ctx context.Context, ptmx *os.File, ws *Adapter, inLog io.Writer, outLog io.Writer) {
	// Create channels to signal completion
	wsDone := make(chan struct{})
	ptyDone := make(chan struct{})

	// Handle WebSocket -> PTY (for binary data and control messages)
	go func() {
		defer close(wsDone)
		for {
			messageType, data, err := ws.conn.ReadMessage()
			if err != nil {
				return
			}

			switch messageType {
			case gorillaws.BinaryMessage:
				inLog.Write(data)
				ptmx.Write(data)
			case gorillaws.TextMessage:
				// Handle control messages
				var msg ControlMessage
				if err := json.Unmarshal(data, &msg); err == nil {
					if msg.Type == "resize" && msg.Cols > 0 && msg.Rows > 0 {
						if c.Logger != nil {
							c.Logger.Debug("Received resize message", "cols", msg.Cols, "rows", msg.Rows)
						}
						// Apply resize to PTY
						if err := creackpty.Setsize(ptmx, &creackpty.Winsize{
							Cols: msg.Cols,
							Rows: msg.Rows,
						}); err != nil {
							if c.Logger != nil {
								c.Logger.Warn("Failed to resize PTY", "error", err)
							}
						}
					}
				}
			}
		}
	}()

	// Handle PTY -> WebSocket
	go func() {
		defer close(ptyDone)
		writer := io.MultiWriter(ws, outLog)
		io.Copy(writer, ptmx)
		if c.Logger != nil {
			c.Logger.Debug("PTY closed, stopping I/O copy")
		}
	}()

	// Wait for either WebSocket or PTY to close
	select {
	case <-wsDone:
		if c.Logger != nil {
			c.Logger.Debug("WebSocket closed, terminating PTY I/O")
		}
	case <-ptyDone:
		if c.Logger != nil {
			c.Logger.Debug("PTY closed, terminating WebSocket I/O")
		}
	}
}

// runWithNewPTY runs command with newly allocated PTY
func (c *ServerCommand) runWithNewPTY(ctx context.Context, cmd *exec.Cmd, ws *Adapter, inLog io.Writer, outLog io.Writer) int {
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

	// Debug logging
	if c.Logger != nil {
		c.Logger.Debug("Starting command with PTY", "cmd", cmd.Args)
	}

	// Start command with PTY using creack/pty
	ptmx, err := creackpty.Start(cmd)
	if err != nil {
		if c.Logger != nil {
			c.Logger.Error("Failed to start with PTY", "error", err)
		}
		return -1
	}
	defer ptmx.Close()

	// Set initial terminal size if specified
	if c.InitialCols > 0 && c.InitialRows > 0 {
		if err := creackpty.Setsize(ptmx, &creackpty.Winsize{
			Cols: c.InitialCols,
			Rows: c.InitialRows,
		}); err != nil {
			if c.Logger != nil {
				c.Logger.Warn("Failed to set initial PTY size", "error", err, "cols", c.InitialCols, "rows", c.InitialRows)
			}
		} else {
			if c.Logger != nil {
				c.Logger.Debug("Set initial PTY size", "cols", c.InitialCols, "rows", c.InitialRows)
			}
		}
	}

	if c.Logger != nil {
		c.Logger.Debug("PTY created successfully")
	}

	c.handlePTYIO(ctx, ptmx, ws, inLog, outLog)

	// Wait for command
	cmdErr := cmd.Wait()

	// Get exit code
	if cmdErr != nil {
		if exitErr, ok := cmdErr.(*exec.ExitError); ok {
			return exitErr.ExitCode()
		}
		return -1
	}
	return 0
}

// runWithConsoleSocket runs command using crun's --console-socket feature
func (c *ServerCommand) runWithConsoleSocket(ctx context.Context, cmd *exec.Cmd, ws *Adapter, inLog io.Writer, outLog io.Writer) int {
	// Create TTY manager with the specified socket path
	tty, err := container.NewWithPath(c.ConsoleSocketPath)
	if err != nil {
		if c.Logger != nil {
			c.Logger.Error("Failed to create TTY manager", "error", err)
		}
		return -1
	}
	defer tty.Close()

	// Set environment to tell exec.sh to use console-socket
	if cmd.Env == nil {
		cmd.Env = os.Environ()
	}
	cmd.Env = append(cmd.Env, "TERM=xterm")
	cmd.Env = append(cmd.Env, fmt.Sprintf("CONSOLE_SOCKET=%s", c.ConsoleSocketPath))

	// Start the command (without PTY - crun will create it)
	cmd.Stdin = nil
	cmd.Stdout = nil
	cmd.Stderr = nil

	if c.Logger != nil {
		c.Logger.Debug("Starting command with console-socket", "cmd", cmd.Args, "socket", c.ConsoleSocketPath)
	}

	if err := cmd.Start(); err != nil {
		if c.Logger != nil {
			c.Logger.Error("Failed to start command", "error", err)
		}
		return -1
	}

	// Wait for crun to send us the PTY
	ptyFile, err := tty.Get()
	if err != nil {
		if c.Logger != nil {
			c.Logger.Error("Failed to receive PTY from console socket", "error", err)
		}
		cmd.Process.Kill()
		cmd.Wait()
		return -1
	}
	defer ptyFile.Close()

	if c.Logger != nil {
		c.Logger.Debug("Received PTY from console socket")
	}

	// Configure the PTY for proper operation
	if err := configurePTY(ptyFile); err != nil {
		if c.Logger != nil {
			c.Logger.Warn("Failed to configure PTY", "error", err)
		}
		// Continue anyway - PTY will work but might have echo issues
	}

	// Set initial terminal size if specified
	if c.InitialCols > 0 && c.InitialRows > 0 {
		if err := creackpty.Setsize(ptyFile, &creackpty.Winsize{
			Cols: c.InitialCols,
			Rows: c.InitialRows,
		}); err != nil {
			if c.Logger != nil {
				c.Logger.Warn("Failed to set initial PTY size", "error", err, "cols", c.InitialCols, "rows", c.InitialRows)
			}
		} else {
			if c.Logger != nil {
				c.Logger.Debug("Set initial PTY size", "cols", c.InitialCols, "rows", c.InitialRows)
			}
		}
	}

	c.handlePTYIO(ctx, ptyFile, ws, inLog, outLog)

	// Wait for command
	cmdErr := cmd.Wait()

	// Get exit code
	if cmdErr != nil {
		if exitErr, ok := cmdErr.(*exec.ExitError); ok {
			return exitErr.ExitCode()
		}
		return -1
	}
	return 0
}

// runWithoutPTY runs command without PTY
func (c *ServerCommand) runWithoutPTY(ctx context.Context, cmd *exec.Cmd, ws *Adapter, inLog io.Writer, outLog io.Writer, errLog io.Writer) int {
	// Set up pipes
	stdin, err := cmd.StdinPipe()
	if err != nil {
		return -1
	}
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		return -1
	}
	stderr, err := cmd.StderrPipe()
	if err != nil {
		return -1
	}

	// Start command
	if err := cmd.Start(); err != nil {
		return -1
	}

	// Create readers/writers for the WebSocket streams
	stdinReader := &streamReader{ws: ws, streamID: StreamStdin}
	stdoutWriter := &streamWriter{ws: ws, streamID: StreamStdout}
	stderrWriter := &streamWriter{ws: ws, streamID: StreamStderr}

	go func() {
		defer stdin.Close()
		r := io.TeeReader(stdinReader, inLog)
		io.Copy(stdin, r)
	}()

	go func() {
		w := io.MultiWriter(stdoutWriter, outLog)
		io.Copy(w, stdout)
	}()

	go func() {
		w := io.MultiWriter(stderrWriter, errLog)
		io.Copy(w, stderr)
	}()

	// Wait for command to complete
	err = cmd.Wait()

	// Return exit code
	if err != nil {
		if exitErr, ok := err.(*exec.ExitError); ok {
			return exitErr.ExitCode()
		}
		return -1
	}
	return 0
}

type lineLogger struct {
	logger *slog.Logger
	stream string
	mu     sync.Mutex
	buf    bytes.Buffer
}

func newLogger(name string, l *slog.Logger) *lineLogger {
	return &lineLogger{
		logger: l,
		stream: name,
	}
}

func (l *lineLogger) Write(p []byte) (int, error) {
	if l == nil {
		return len(p), nil
	}
	l.mu.Lock()
	defer l.mu.Unlock()
	n := len(p)
	l.buf.Write(p)
	for {
		line, err := l.buf.ReadString('\n')
		if err != nil {
			break
		}
		line = strings.TrimSuffix(line, "\n")
		l.logger.Info("io", "stream", l.stream, "line", line)
	}
	return n, nil
}

func (l *lineLogger) Close() {
	if l == nil {
		return
	}

	l.mu.Lock()
	defer l.mu.Unlock()
	if l.logger != nil && l.buf.Len() > 0 {
		line := strings.TrimRight(l.buf.String(), "\n")
		l.logger.Info("io", "stream", l.stream, "line", line)
	}
	l.buf.Reset()
}
