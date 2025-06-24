package wsexec

import (
	"context"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"os"
	"os/exec"
	"strings"
	"time"

	creackpty "github.com/creack/pty"
	gorillaws "github.com/gorilla/websocket"
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

	// Console socket path for receiving PTY from crun
	ConsoleSocketPath string

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

	if c.Logger != nil {
		c.Logger.Info("ServerCommand.Handle: WebSocket upgrade successful")
	}

	adapter := NewAdapter(conn)
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
			// Use console socket to receive PTY from crun
			return c.runWithConsoleSocket(ctx, cmd, ws)
		} else {
			// Allocate new PTY ourselves
			return c.runWithNewPTY(ctx, cmd, ws)
		}
	} else {
		// No PTY
		return c.runWithoutPTY(ctx, cmd, ws)
	}
}

// runWithNewPTY runs command with newly allocated PTY
func (c *ServerCommand) runWithNewPTY(ctx context.Context, cmd *exec.Cmd, ws *Adapter) int {
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
		ws.WriteError(err)
		return -1
	}
	defer ptmx.Close()

	if c.Logger != nil {
		c.Logger.Debug("PTY created successfully")
	}

	// Handle PTY I/O
	ctx, cancel := context.WithCancel(ctx)
	defer cancel()

	// Channel to signal I/O completion
	ioDone := make(chan struct{}, 3)

	// Handle WebSocket -> PTY
	go func() {
		c.handleWebSocketToPTY(ctx, ws, ptmx)
		ioDone <- struct{}{}
	}()

	// Handle PTY -> WebSocket
	go func() {
		c.handlePTYToWebSocket(ctx, ptmx, ws)
		ioDone <- struct{}{}
	}()

	// Handle ping/pong
	go func() {
		c.handlePings(ctx, ws)
		ioDone <- struct{}{}
	}()

	// Wait for command
	cmdErr := cmd.Wait()

	// Cancel context immediately to stop I/O goroutines
	cancel()

	// Close the PTY immediately when command exits
	// This ensures that any readers get EOF
	ptmx.Close()

	// Wait for I/O to finish with a shorter timeout
	done := make(chan struct{})
	go func() {
		for i := 0; i < 3; i++ {
			<-ioDone
		}
		close(done)
	}()

	select {
	case <-done:
		// All I/O completed cleanly
		if c.Logger != nil {
			c.Logger.Debug("All I/O goroutines completed cleanly")
		}
	case <-time.After(100 * time.Millisecond):
		// Very short timeout since PTY close should trigger immediate EOF
		if c.Logger != nil {
			c.Logger.Debug("I/O cleanup timed out (this is normal)")
		}
	}

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
func (c *ServerCommand) runWithConsoleSocket(ctx context.Context, cmd *exec.Cmd, ws *Adapter) int {
	// Create console socket
	consoleSocket, err := NewConsoleSocket(c.ConsoleSocketPath)
	if err != nil {
		if c.Logger != nil {
			c.Logger.Error("Failed to create console socket", "error", err)
		}
		ws.WriteError(err)
		return -1
	}
	defer consoleSocket.Close()

	// Start listening for PTY FD
	consoleSocket.Start()

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
		ws.WriteError(err)
		return -1
	}

	// Wait for crun to send us the PTY
	ptyFile, err := consoleSocket.WaitForPTY()
	if err != nil {
		if c.Logger != nil {
			c.Logger.Error("Failed to receive PTY from console socket", "error", err)
		}
		ws.WriteError(err)
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

	// Now handle I/O with the PTY we received from crun
	ctx, cancel := context.WithCancel(ctx)
	defer cancel()

	// Channel to signal I/O completion
	ioDone := make(chan struct{}, 3)

	// Handle WebSocket -> PTY
	go func() {
		c.handleWebSocketToPTY(ctx, ws, ptyFile)
		ioDone <- struct{}{}
	}()

	// Handle PTY -> WebSocket
	go func() {
		c.handlePTYToWebSocket(ctx, ptyFile, ws)
		ioDone <- struct{}{}
	}()

	// Handle ping/pong
	go func() {
		c.handlePings(ctx, ws)
		ioDone <- struct{}{}
	}()

	// Wait for command
	cmdErr := cmd.Wait()

	// Cancel context immediately to stop I/O goroutines
	cancel()

	// Close the PTY immediately when command exits
	ptyFile.Close()

	// Wait for I/O to finish with a shorter timeout
	done := make(chan struct{})
	go func() {
		for i := 0; i < 3; i++ {
			<-ioDone
		}
		close(done)
	}()

	select {
	case <-done:
		// All I/O completed cleanly
		if c.Logger != nil {
			c.Logger.Debug("All I/O goroutines completed cleanly")
		}
	case <-time.After(100 * time.Millisecond):
		// Very short timeout since PTY close should trigger immediate EOF
		if c.Logger != nil {
			c.Logger.Debug("I/O cleanup timed out (this is normal)")
		}
	}

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
func (c *ServerCommand) runWithoutPTY(ctx context.Context, cmd *exec.Cmd, ws *Adapter) int {
	// Set up pipes
	stdin, err := cmd.StdinPipe()
	if err != nil {
		ws.WriteError(err)
		return -1
	}
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		ws.WriteError(err)
		return -1
	}
	stderr, err := cmd.StderrPipe()
	if err != nil {
		ws.WriteError(err)
		return -1
	}

	// Start command
	if err := cmd.Start(); err != nil {
		ws.WriteError(err)
		return -1
	}

	ctx, cancel := context.WithCancel(ctx)
	defer cancel()

	// Channel to signal I/O completion
	ioDone := make(chan struct{}, 3)

	// Handle stdin
	go func() {
		defer stdin.Close()
		c.handleWebSocketInput(ctx, ws, stdin)
		ioDone <- struct{}{}
	}()

	// Handle stdout
	go func() {
		c.streamToWebSocket(ctx, stdout, ws, MessageTypeStdout)
		ioDone <- struct{}{}
	}()

	// Handle stderr
	go func() {
		c.streamToWebSocket(ctx, stderr, ws, MessageTypeStderr)
		ioDone <- struct{}{}
	}()

	// Wait for command
	err = cmd.Wait()
	cancel()

	// Wait for I/O to complete
	for i := 0; i < 3; i++ {
		<-ioDone
	}

	if err != nil {
		if exitErr, ok := err.(*exec.ExitError); ok {
			return exitErr.ExitCode()
		}
		return -1
	}
	return 0
}

// handleWebSocketToPTY handles input from WebSocket to PTY
func (c *ServerCommand) handleWebSocketToPTY(ctx context.Context, ws *Adapter, ptmx io.Writer) {
	for {
		select {
		case <-ctx.Done():
			return
		default:
			msg, err := ws.ReadMessage()
			if err != nil {
				return
			}

			switch msg.Type {
			case MessageTypeStdin:
				if _, err := ptmx.Write(msg.Data); err != nil {
					return
				}
			case MessageTypeStdinEOF:
				// PTY doesn't have a separate stdin to close
				// Just ignore EOF and continue - the PTY will close when the process exits
				continue
			case MessageTypeResize:
				// Handle resize if PTY supports it
				width, height, _ := DecodeResize(msg.Data)

				// Try the Setsize method first (for creack/pty objects)
				if resizer, ok := ptmx.(interface{ Setsize(rows, cols uint16) error }); ok {
					if err := resizer.Setsize(height, width); err != nil && c.Logger != nil {
						c.Logger.Warn("Failed to resize PTY", "error", err)
					}
				} else if f, ok := ptmx.(*os.File); ok {
					// For plain file descriptors (like from console socket), use creack/pty
					winsize := &creackpty.Winsize{
						Rows: height,
						Cols: width,
					}
					if err := creackpty.Setsize(f, winsize); err != nil && c.Logger != nil {
						c.Logger.Warn("Failed to resize PTY file", "error", err)
					} else if c.Logger != nil {
						c.Logger.Debug("Resized PTY", "width", width, "height", height)
					}
				}
			case MessageTypePing:
				ws.WritePong()
			}
		}
	}
}

// handlePTYToWebSocket handles output from PTY to WebSocket
func (c *ServerCommand) handlePTYToWebSocket(ctx context.Context, ptmx io.Reader, ws *Adapter) {
	buf := make([]byte, 4096)
	totalRead := 0

	// Use a goroutine to perform the blocking read
	readChan := make(chan struct {
		n   int
		err error
	}, 1)

	go func() {
		defer close(readChan)
		for {
			n, err := ptmx.Read(buf)
			select {
			case readChan <- struct {
				n   int
				err error
			}{n, err}:
				if err != nil {
					return // EOF or other error - stop reading
				}
			case <-ctx.Done():
				return // Context cancelled
			}
		}
	}()

	for {
		select {
		case <-ctx.Done():
			if c.Logger != nil {
				c.Logger.Debug("PTY reader: context done", "totalRead", totalRead)
			}
			return
		case result, ok := <-readChan:
			if !ok {
				// Channel closed - reader goroutine exited
				if c.Logger != nil {
					c.Logger.Debug("PTY reader: read channel closed", "totalRead", totalRead)
				}
				return
			}

			if result.n > 0 {
				totalRead += result.n
				if c.Logger != nil {
					c.Logger.Debug("PTY reader: read data", "bytes", result.n, "data", string(buf[:result.n]))
				}
				if err := ws.WriteStdout(buf[:result.n]); err != nil {
					if c.Logger != nil {
						c.Logger.Error("PTY reader: write error", "error", err)
					}
					return
				}
			}

			if result.err != nil {
				// EOF is expected when command finishes, don't log as error
				if c.Logger != nil && result.err != io.EOF {
					c.Logger.Debug("PTY reader: read error", "error", result.err, "totalRead", totalRead)
				} else if c.Logger != nil && result.err == io.EOF {
					c.Logger.Debug("PTY reader: command completed", "totalRead", totalRead)
				}
				return
			}
		}
	}
}

// handleWebSocketInput handles stdin from WebSocket
func (c *ServerCommand) handleWebSocketInput(ctx context.Context, ws *Adapter, stdin io.Writer) {
	stdinCloser, ok := stdin.(io.Closer)
	for {
		select {
		case <-ctx.Done():
			return
		default:
			msg, err := ws.ReadMessage()
			if err != nil {
				return
			}

			switch msg.Type {
			case MessageTypeStdin:
				if _, err := stdin.Write(msg.Data); err != nil {
					return
				}
			case MessageTypeStdinEOF:
				// Close stdin to signal EOF to the command
				if ok {
					stdinCloser.Close()
				}
				return
			case MessageTypePing:
				ws.WritePong()
			}
		}
	}
}

// streamToWebSocket streams from reader to WebSocket
func (c *ServerCommand) streamToWebSocket(ctx context.Context, r io.Reader, ws *Adapter, msgType MessageType) {
	buf := make([]byte, 4096)
	for {
		select {
		case <-ctx.Done():
			return
		default:
			n, err := r.Read(buf)
			if n > 0 {
				var writeErr error
				switch msgType {
				case MessageTypeStdout:
					writeErr = ws.WriteStdout(buf[:n])
				case MessageTypeStderr:
					writeErr = ws.WriteStderr(buf[:n])
				}
				if writeErr != nil {
					return
				}
			}
			if err != nil {
				return
			}
		}
	}
}

// handlePings handles ping/pong keepalive
func (c *ServerCommand) handlePings(ctx context.Context, ws *Adapter) {
	ticker := time.NewTicker(5 * time.Second)
	defer ticker.Stop()

	for {
		select {
		case <-ctx.Done():
			return
		case <-ticker.C:
			if err := ws.Ping(); err != nil {
				return
			}
		}
	}
}
