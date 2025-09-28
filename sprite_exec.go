package sprites

import (
	"context"
	"errors"
	"fmt"
	"io"
	"net/http"
	"net/url"
	"sync"
	"syscall"
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
	c.wsCmd = newWSCmdContext(c.ctx, req, c.Path, c.Args[1:]...)

	// Set up I/O
	c.setupIO()

	// Set TTY mode
	c.wsCmd.Tty = c.tty

	// Start goroutines for pipe handling
	for _, fn := range c.goroutines {
		go fn()
	}

	// Start the WebSocket command
	if err := c.wsCmd.Start(); err != nil {
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

// SetTTYSize sets the initial terminal size for TTY mode.
// This must be called before Start().
func (c *Cmd) SetTTYSize(rows, cols uint16) error {
	c.mu.Lock()
	defer c.mu.Unlock()

	if c.started {
		return errors.New("sprite: SetTTYSize after process started")
	}
	if !c.tty {
		return errors.New("sprite: SetTTYSize called but TTY mode not enabled")
	}

	c.ttySize = &ttySize{Rows: rows, Cols: cols}
	return nil
}

// Resize changes the terminal size of a running TTY command.
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

	return c.wsCmd.Resize(cols, rows)
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

	// Build path
	u.Path = fmt.Sprintf("/sprites/%s/exec", c.sprite.name)

	// Build query parameters
	q := u.Query()

	// Add command arguments
	for i, arg := range c.Args {
		q.Add("cmd", arg)
		if i == 0 {
			q.Set("path", arg)
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

// Sys returns the system-specific exit information.
// On Unix, this is a syscall.WaitStatus.
func (e *ExitError) Sys() interface{} {
	// Create a WaitStatus that indicates the process exited with e.Code
	return syscall.WaitStatus(e.Code << 8)
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
