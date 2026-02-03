package sprites

import (
	"context"
	"errors"
	"fmt"
	"io"
	"net/http"
	"net/url"
	"strings"
	"sync"
)

// ErrNotStarted is returned when Wait is called before Start.
var ErrNotStarted = errors.New("sprite: command not started")

// Cmd represents a command to be run on a sprite.
// It mirrors the API of exec.Cmd for compatibility.
type Cmd struct {
	// Path is the path of the command to run.
	Path string

	// Args holds command line arguments, including the command as Args[0].
	Args []string

	// Env specifies the environment of the process.
	// Each entry is of the form "key=value".
	// If Env is nil, the new process uses the current process's environment.
	Env []string

	// Dir specifies the working directory of the command.
	// If Dir is the empty string, the command runs in the sprite's default directory.
	Dir string

	// Stdin specifies the process's standard input.
	// If Stdin is nil, the process reads from the null device (os.DevNull).
	// If Stdin is an *os.File, the process's standard input is connected
	// directly to that file.
	// Otherwise, during the execution of the command a separate
	// goroutine reads from Stdin and delivers that data to the command
	// over the network. In this case, Wait does not complete until the goroutine
	// stops copying, either because it has reached the end of Stdin
	// (EOF or a read error) or because writing to the network returned an error.
	Stdin io.Reader

	// Stdout and Stderr specify the process's standard output and error.
	// If either is nil, the command uses the null device (os.DevNull).
	// If either is an *os.File, the process's corresponding output
	// is connected directly to that file.
	// Otherwise, during the execution of the command a separate goroutine
	// reads from the network and delivers that data to the corresponding Writer.
	// In this case, Wait does not complete until the goroutine reaches EOF or
	// encounters an error.
	Stdout io.Writer
	Stderr io.Writer

	// Process-specific state
	ctx    context.Context
	sprite *Sprite
	wsCmd  *wsCmd

	// Synchronization
	mu       sync.Mutex
	started  bool
	finished bool
	waitErr  error
	exitCode int

	// Pipe management
	stdinPipe  *writePipe
	stdoutPipe *readPipe
	stderrPipe *readPipe
	closers    []io.Closer
	goroutines []func() error

	// TTY support
	tty     bool
	ttySize *ttySize

	// Cell-sync mode (mosh-like screen synchronization)
	cellSync bool

	// Session management
	sessionID   string
	controlMode bool

	// TextMessageHandler is called when text messages are received from the server.
	// This is typically used for port notifications or other out-of-band messages.
	// The handler is called with the raw message data.
	//
	// Example usage for handling port notifications:
	//
	//     import "encoding/json"
	//
	//     cmd.TextMessageHandler = func(data []byte) {
	//         var notification sprites.PortNotificationMessage
	//         if err := json.Unmarshal(data, &notification); err != nil {
	//             log.Printf("Failed to parse notification: %v", err)
	//             return
	//         }
	//
	//         switch notification.Type {
	//         case "port_opened":
	//             fmt.Printf("Port %d opened by PID %d\n", notification.Port, notification.PID)
	//             // Start local proxy or take other action
	//         case "port_closed":
	//             fmt.Printf("Port %d closed by PID %d\n", notification.Port, notification.PID)
	//             // Stop local proxy or take other action
	//         }
	//     }
	TextMessageHandler func([]byte)
}

// ttySize represents terminal dimensions
type ttySize struct {
	Rows uint16
	Cols uint16
}

// Command returns a new Cmd to execute the named program with the given arguments on the sprite.
func (s *Sprite) Command(name string, arg ...string) *Cmd {
	cmd := &Cmd{
		Path:   name,
		Args:   append([]string{name}, arg...),
		ctx:    context.Background(),
		sprite: s,
	}
	return cmd
}

// CommandContext is like Command but includes a context.
// The provided context is used to kill the process (by calling os.Process.Kill)
// if the context becomes done before the command completes on its own.
func (s *Sprite) CommandContext(ctx context.Context, name string, arg ...string) *Cmd {
	if ctx == nil {
		panic("sprite: CommandContext called with nil context")
	}
	cmd := s.Command(name, arg...)
	cmd.ctx = ctx
	return cmd
}

// String returns a human-readable description of c.
// It is intended only for debugging.
func (c *Cmd) String() string {
	if c == nil {
		return "<nil>"
	}
	return fmt.Sprintf("%s %v", c.Path, c.Args[1:])
}

// Run starts the specified command and waits for it to complete.
func (c *Cmd) Run() error {
	if err := c.Start(); err != nil {
		return err
	}
	return c.Wait()
}

// Start starts the specified command but does not wait for it to complete.
func (c *Cmd) Start() error {
	c.mu.Lock()
	defer c.mu.Unlock()

	if c.started {
		return errors.New("sprite: already started")
	}
	c.started = true

	// Close any existing pipes on error
	closeDescriptors := func(closers []io.Closer) {
		for _, fd := range closers {
			fd.Close()
		}
	}

	// For attach operations, ensure we know the sprite's version to select the right endpoint
	if c.sessionID != "" && c.sprite.client.SpriteVersion() == "" {
		if err := c.sprite.client.FetchVersion(c.ctx, c.sprite.name); err != nil {
			closeDescriptors(c.closers)
			return fmt.Errorf("failed to fetch sprite version: %w", err)
		}
	}

	// Build WebSocket URL
	wsURL, err := c.buildWebSocketURL()
	if err != nil {
		closeDescriptors(c.closers)
		return err
	}

	// Create HTTP request with auth
	req, err := http.NewRequestWithContext(c.ctx, "GET", wsURL.String(), nil)
	if err != nil {
		closeDescriptors(c.closers)
		return err
	}
	req.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.sprite.client.token))

	// Create WebSocket command
	var args []string
	if len(c.Args) > 1 {
		args = c.Args[1:]
	}
	c.wsCmd = newWSCmdContext(c.ctx, req, c.Path, args...)

	// Set up I/O
	c.setupIO()

	// Set TTY mode, cell-sync, and attach flag
	c.wsCmd.Tty = c.tty
	c.wsCmd.CellSync = c.cellSync
	c.wsCmd.IsAttach = c.sessionID != ""

	// Set text message handler if provided
	if c.TextMessageHandler != nil {
		c.wsCmd.TextMessageHandler = c.TextMessageHandler
	}

	// Start goroutines for pipe handling
	for _, fn := range c.goroutines {
		go fn()
	}

	// Start the WebSocket command
	if err := c.wsCmd.Start(); err != nil {
		// Check for 404 - sprite may need legacy endpoint format
		if c.sessionID != "" && !c.sprite.useLegacyExecEndpoint && strings.Contains(err.Error(), "HTTP 404") {
			// Mark sprite as requiring legacy format and force TTY mode
			c.sprite.useLegacyExecEndpoint = true
			c.tty = true

			// Rebuild URL with legacy query parameter format
			wsURL, err = c.buildWebSocketURL()
			if err != nil {
				closeDescriptors(c.closers)
				return err
			}

			// Create new request and wsCmd for retry
			req, err = http.NewRequestWithContext(c.ctx, "GET", wsURL.String(), nil)
			if err != nil {
				closeDescriptors(c.closers)
				return err
			}
			req.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.sprite.client.token))

			c.wsCmd = newWSCmdContext(c.ctx, req, c.Path, args...)
			c.setupIO()
			c.wsCmd.Tty = c.tty
			c.wsCmd.CellSync = c.cellSync
			c.wsCmd.IsAttach = true
			if c.TextMessageHandler != nil {
				c.wsCmd.TextMessageHandler = c.TextMessageHandler
			}

			// Retry with legacy endpoint
			if retryErr := c.wsCmd.Start(); retryErr != nil {
				closeDescriptors(c.closers)
				return fmt.Errorf("failed to start sprite command: %w", retryErr)
			}
			return nil
		}

		closeDescriptors(c.closers)
		return fmt.Errorf("failed to start sprite command: %w", err)
	}

	return nil
}

// Wait waits for the command to exit and waits for any copying to stdin or
// copying from stdout or stderr to complete.
func (c *Cmd) Wait() error {
	c.mu.Lock()
	if !c.started {
		c.mu.Unlock()
		return ErrNotStarted
	}
	if c.finished {
		err := c.waitErr
		c.mu.Unlock()
		return err
	}
	c.mu.Unlock()

	// Wait for the command
	if c.wsCmd == nil {
		return errors.New("sprite: command not fully initialized")
	}
	err := c.wsCmd.Wait()

	// Get exit code
	c.exitCode = c.wsCmd.ExitCode()

	// Close write end of stdin pipe
	if c.stdinPipe != nil {
		c.stdinPipe.Close()
	}

	// Wait for I/O goroutines
	var copyError error
	for _, fn := range c.goroutines {
		if err := fn(); err != nil && copyError == nil {
			copyError = err
		}
	}

	// Close all descriptors
	for _, closer := range c.closers {
		closer.Close()
	}

	c.mu.Lock()
	c.finished = true

	// Determine final error
	if err != nil {
		c.waitErr = err
	} else if c.exitCode != 0 {
		c.waitErr = &ExitError{Code: c.exitCode}
	} else if copyError != nil {
		c.waitErr = copyError
	}

	err = c.waitErr
	c.mu.Unlock()

	return err
}

// Output runs the command and returns its standard output.
func (c *Cmd) Output() ([]byte, error) {
	if c.Stdout != nil {
		return nil, errors.New("sprite: Stdout already set")
	}
	var stdout []byte
	c.Stdout = &outputBuffer{bytes: &stdout}

	err := c.Run()
	return stdout, err
}

// CombinedOutput runs the command and returns its combined standard
// output and standard error.
func (c *Cmd) CombinedOutput() ([]byte, error) {
	if c.Stdout != nil {
		return nil, errors.New("sprite: Stdout already set")
	}
	if c.Stderr != nil {
		return nil, errors.New("sprite: Stderr already set")
	}
	var b []byte
	out := &outputBuffer{bytes: &b}
	c.Stdout = out
	c.Stderr = out

	err := c.Run()
	return b, err
}

// StdinPipe returns a pipe that will be connected to the command's
// standard input when the command starts.
func (c *Cmd) StdinPipe() (io.WriteCloser, error) {
	if c.Stdin != nil {
		return nil, errors.New("sprite: Stdin already set")
	}
	if c.started {
		return nil, errors.New("sprite: StdinPipe after process started")
	}
	pr, pw := io.Pipe()
	c.Stdin = pr
	wp := &writePipe{WriteCloser: pw}
	c.stdinPipe = wp
	c.closers = append(c.closers, pr)
	return wp, nil
}

// StdoutPipe returns a pipe that will be connected to the command's
// standard output when the command starts.
func (c *Cmd) StdoutPipe() (io.ReadCloser, error) {
	if c.Stdout != nil {
		return nil, errors.New("sprite: Stdout already set")
	}
	if c.started {
		return nil, errors.New("sprite: StdoutPipe after process started")
	}
	pr, pw := io.Pipe()
	c.Stdout = pw
	rp := &readPipe{ReadCloser: pr}
	c.stdoutPipe = rp
	c.closers = append(c.closers, pw)
	return rp, nil
}

// StderrPipe returns a pipe that will be connected to the command's
// standard error when the command starts.
func (c *Cmd) StderrPipe() (io.ReadCloser, error) {
	if c.Stderr != nil {
		return nil, errors.New("sprite: Stderr already set")
	}
	if c.started {
		return nil, errors.New("sprite: StderrPipe after process started")
	}
	pr, pw := io.Pipe()
	c.Stderr = pw
	rp := &readPipe{ReadCloser: pr}
	c.stderrPipe = rp
	c.closers = append(c.closers, pw)
	return rp, nil
}

// SetTTY enables or disables TTY mode for the command.
// When TTY mode is enabled, the command runs with a pseudo-terminal.
func (c *Cmd) SetTTY(enable bool) {
	c.mu.Lock()
	defer c.mu.Unlock()

	if c.started {
		panic("sprite: SetTTY after process started")
	}
	c.tty = enable
}

// SetCellSync enables or disables cell-sync mode for the command.
// Cell-sync provides mosh-like screen state synchronization instead of raw byte streaming.
// This mode is only effective when TTY mode is also enabled.
// When enabled, the client receives screen state diffs instead of raw terminal output.
func (c *Cmd) SetCellSync(enable bool) {
	c.mu.Lock()
	defer c.mu.Unlock()

	if c.started {
		panic("sprite: SetCellSync after process started")
	}
	c.cellSync = enable
}

// IsCellSync returns true if cell-sync mode was negotiated successfully.
// This should only be called after Start() returns.
func (c *Cmd) IsCellSync() bool {
	c.mu.Lock()
	defer c.mu.Unlock()

	if c.wsCmd != nil {
		return c.wsCmd.IsCellSync()
	}
	return false
}

// SetCellSyncHandler sets a callback for screen updates in cell-sync mode.
// The handler is called whenever the screen state is updated.
// This should be called before Start().
func (c *Cmd) SetCellSyncHandler(handler func(*ScreenSnapshot)) {
	c.mu.Lock()
	defer c.mu.Unlock()

	if c.started && c.wsCmd != nil {
		c.wsCmd.SetCellSyncHandler(handler)
	}
}

// GetCellSyncSession returns the cell-sync session for direct access.
// Returns nil if not in cell-sync mode.
func (c *Cmd) GetCellSyncSession() *CellSyncSession {
	c.mu.Lock()
	defer c.mu.Unlock()

	if c.wsCmd != nil {
		return c.wsCmd.GetCellSyncSession()
	}
	return nil
}

// SendCellSyncInput sends a key event in cell-sync mode.
func (c *Cmd) SendCellSyncInput(event KeyEvent) error {
	c.mu.Lock()
	defer c.mu.Unlock()

	if c.wsCmd != nil {
		return c.wsCmd.SendCellSyncInput(event)
	}
	return nil
}

// SetTTYSize sets the terminal size for TTY mode.
// If called before Start(), it sets the initial size.
// If called after Start(), it resizes the running terminal.
func (c *Cmd) SetTTYSize(rows, cols uint16) error {
	c.mu.Lock()
	defer c.mu.Unlock()

	if !c.tty {
		return errors.New("sprite: SetTTYSize called but TTY mode not enabled")
	}

	// If process is already started, resize the running terminal
	if c.started && !c.finished {
		if c.wsCmd == nil {
			return errors.New("sprite: command not fully initialized")
		}
		return c.wsCmd.Resize(cols, rows)
	}

	// Otherwise set the initial size
	c.ttySize = &ttySize{Rows: rows, Cols: cols}
	return nil
}

// Resize changes the terminal size of a running TTY command.
// Deprecated: Use SetTTYSize instead, which works both before and after Start().
func (c *Cmd) Resize(rows, cols uint16) error {
	c.mu.Lock()
	defer c.mu.Unlock()

	if !c.started {
		return errors.New("sprite: Resize before process started")
	}
	if !c.tty {
		return errors.New("sprite: Resize called but TTY mode not enabled")
	}
	if c.finished {
		return errors.New("sprite: Resize after process finished")
	}
	if c.wsCmd == nil {
		return errors.New("sprite: command not fully initialized")
	}

	return c.wsCmd.Resize(cols, rows)
}

// Signal sends a signal to the remote process.
// If the server supports WebSocket signals (advertised via X-Sprite-Capabilities header),
// it sends the signal over the existing WebSocket connection. Otherwise, it falls back
// to an HTTP POST request to the kill endpoint.
// Valid signal names: INT, TERM, HUP, KILL, QUIT, USR1, USR2
func (c *Cmd) Signal(signal string) error {
	c.mu.Lock()
	defer c.mu.Unlock()

	if !c.started {
		return errors.New("sprite: Signal before process started")
	}
	if c.finished {
		return errors.New("sprite: Signal after process finished")
	}

	// Use WebSocket if server supports it
	if c.wsCmd.HasCapability("signal") {
		return c.wsCmd.Signal(signal)
	}

	// Fall back to HTTP POST
	// Use session ID from attach or from session_info message
	sessID := c.sessionID
	if sessID == "" {
		sessID = c.wsCmd.SessionID()
	}
	if sessID == "" {
		return errors.New("sprite: no session ID for HTTP signal fallback")
	}
	return c.sprite.client.signalSession(c.ctx, c.sprite.name, sessID, signal)
}

// ExitCode returns the exit code of the exited process, or -1
// if the process hasn't exited or was terminated by a signal.
func (c *Cmd) ExitCode() int {
	c.mu.Lock()
	defer c.mu.Unlock()

	if !c.finished {
		return -1
	}
	return c.exitCode
}

// buildWebSocketURL constructs the WebSocket URL for the exec endpoint
func (c *Cmd) buildWebSocketURL() (*url.URL, error) {
	baseURL := c.sprite.client.baseURL

	// Convert HTTP(S) to WS(S)
	if baseURL[:4] == "http" {
		baseURL = "ws" + baseURL[4:]
	}

	// Parse base URL
	u, err := url.Parse(baseURL)
	if err != nil {
		return nil, fmt.Errorf("invalid base URL: %w", err)
	}

	// Build query parameters
	q := u.Query()

	// Build path - endpoint format depends on server version and cached preference
	if c.sessionID != "" {
		// Use legacy format if sprite is known to require it, or if version doesn't support path attach
		if c.sprite.useLegacyExecEndpoint || !c.sprite.client.supportsPathAttach() {
			// Legacy format: query parameter
			u.Path = fmt.Sprintf("/v1/sprites/%s/exec", c.sprite.name)
			q.Set("id", c.sessionID)
		} else {
			// New format: path parameter (try first)
			u.Path = fmt.Sprintf("/v1/sprites/%s/exec/%s", c.sprite.name, c.sessionID)
		}
	} else {
		u.Path = fmt.Sprintf("/v1/sprites/%s/exec", c.sprite.name)
	}

	// Add command arguments (only for new commands, not attach)
	if c.sessionID == "" {
		for i, arg := range c.Args {
			q.Add("cmd", arg)
			if i == 0 {
				q.Set("path", arg)
			}
		}
	}

	// Add environment variables
	for _, env := range c.Env {
		q.Add("env", env)
	}

	// Add working directory
	if c.Dir != "" {
		q.Set("dir", c.Dir)
	}

	// Add TTY settings
	if c.tty {
		q.Set("tty", "true")
		if c.ttySize != nil {
			q.Set("rows", fmt.Sprintf("%d", c.ttySize.Rows))
			q.Set("cols", fmt.Sprintf("%d", c.ttySize.Cols))
		}
	}

	// Add control mode flag
	if c.controlMode {
		q.Set("cc", "true")
	}

	// Add stdin parameter so the server knows whether to expect input
	if c.Stdin == nil {
		q.Set("stdin", "false")
	} else {
		q.Set("stdin", "true")
	}

	u.RawQuery = q.Encode()
	return u, nil
}

// setupIO configures I/O for the WebSocket command
func (c *Cmd) setupIO() {
	// Set stdin
	if c.Stdin == nil {
		c.wsCmd.Stdin = nil
	} else {
		c.wsCmd.Stdin = c.Stdin
	}

	// Set stdout
	if c.Stdout == nil {
		c.wsCmd.Stdout = nil
	} else {
		c.wsCmd.Stdout = c.Stdout
	}

	// Set stderr
	if c.Stderr == nil {
		c.wsCmd.Stderr = nil
	} else {
		c.wsCmd.Stderr = c.Stderr
	}
}

// ExitError reports an unsuccessful exit by a command.
type ExitError struct {
	Code int
}

func (e *ExitError) Error() string {
	return fmt.Sprintf("exit status %d", e.Code)
}

// ExitCode returns the exit code of the exited process.
func (e *ExitError) ExitCode() int {
	return e.Code
}

// writePipe wraps an io.WriteCloser to prevent double closes
type writePipe struct {
	io.WriteCloser
	mu     sync.Mutex
	closed bool
}

func (p *writePipe) Close() error {
	p.mu.Lock()
	defer p.mu.Unlock()
	if !p.closed && p.WriteCloser != nil {
		p.closed = true
		return p.WriteCloser.Close()
	}
	return nil
}

// readPipe wraps an io.ReadCloser to prevent double closes
type readPipe struct {
	io.ReadCloser
	mu     sync.Mutex
	closed bool
}

func (p *readPipe) Close() error {
	p.mu.Lock()
	defer p.mu.Unlock()
	if !p.closed && p.ReadCloser != nil {
		p.closed = true
		return p.ReadCloser.Close()
	}
	return nil
}

// outputBuffer is a thread-safe buffer for capturing output
type outputBuffer struct {
	bytes *[]byte
	mu    sync.Mutex
}

func (b *outputBuffer) Write(p []byte) (n int, err error) {
	b.mu.Lock()
	defer b.mu.Unlock()
	*b.bytes = append(*b.bytes, p...)
	return len(p), nil
}
