package wsexec

import (
	"context"
	"crypto/tls"
	"fmt"
	"io"
	"net/http"
	"os"
	"time"

	gorillaws "github.com/gorilla/websocket"
)

// Command returns a new Cmd for executing remotely via WebSocket
func Command(req *http.Request, name string, arg ...string) *Cmd {
	if req == nil {
		panic("wsexec: Command called with nil request")
	}
	return &Cmd{
		Request:     req,
		Path:        name,
		Args:        append([]string{name}, arg...),
		ctx:         context.Background(),
		startChan:   make(chan error, 1),
		exitChan:    make(chan int, 1),
		doneChan:    make(chan struct{}),
		adapterChan: make(chan *Adapter, 1),
	}
}

// CommandContext is like Command but includes a context
func CommandContext(ctx context.Context, req *http.Request, name string, arg ...string) *Cmd {
	if ctx == nil {
		panic("wsexec: CommandContext called with nil context")
	}
	cmd := Command(req, name, arg...)
	cmd.ctx = ctx
	return cmd
}

// Cmd represents a remote command execution
type Cmd struct {
	// Command to execute
	Path string
	Args []string

	// The prepared HTTP request
	Request *http.Request

	// I/O
	Stdin  io.Reader
	Stdout io.Writer
	Stderr io.Writer

	// Options
	Env []string
	Dir string
	Tty bool

	// PingInterval controls how often to send WebSocket pings (default 5s)
	PingInterval time.Duration

	// Private fields
	ctx    context.Context
	conn   *gorillaws.Conn
	cancel context.CancelFunc // Add cancel function to stop all goroutines

	// Channels for communication
	startChan   chan error    // Signals start completion
	exitChan    chan int      // Sends exit code
	doneChan    chan struct{} // Signals command completion
	adapterChan chan *Adapter // Stores adapter reference

	// For PTY support
	ptyMaster *wsPTY
}

// Run starts the command and waits for it to complete
func (c *Cmd) Run() error {
	if err := c.Start(); err != nil {
		return err
	}
	return c.Wait()
}

// Start starts the command but does not wait for it to complete
func (c *Cmd) Start() error {
	go c.start()

	// Wait for start to complete or fail
	select {
	case err := <-c.startChan:
		return err
	case <-c.ctx.Done():
		return c.ctx.Err()
	}
}

// start performs the actual WebSocket connection and setup
func (c *Cmd) start() {
	defer func() {
		// Debug: log when we're about to close doneChan
		if c.ptyMaster != nil && c.ptyMaster.cmd != nil {
			// For debugging PTY issues
			select {
			case code := <-c.exitChan:
				// Put it back
				select {
				case c.exitChan <- code:
				default:
				}
			default:
			}
		}
		close(c.doneChan) // Always close doneChan
	}()

	// Set up WebSocket dialer
	dialer := gorillaws.DefaultDialer
	dialer.HandshakeTimeout = 10 * time.Second

	// Configure TLS if using wss://
	if c.Request.URL.Scheme == "wss" {
		dialer.TLSClientConfig = &tls.Config{}
	}

	// Connect
	conn, _, err := dialer.DialContext(c.ctx, c.Request.URL.String(), c.Request.Header)
	if err != nil {
		c.startChan <- fmt.Errorf("failed to connect: %w", err)
		return
	}

	c.conn = conn
	adapter := NewAdapter(conn)

	// Send adapter to anyone waiting
	select {
	case c.adapterChan <- adapter:
	default:
	}

	// Send command configuration if needed
	// Note: In this implementation, command configuration is sent via HTTP headers or URL
	// The server should extract command details from the request

	// Signal successful start
	c.startChan <- nil

	// Run the I/O loop
	c.runIO(adapter)
}

// Wait waits for the command to exit
func (c *Cmd) Wait() error {
	select {
	case <-c.doneChan:
		// Command finished
		return nil
	case <-c.ctx.Done():
		return c.ctx.Err()
	}
}

// runIO handles the WebSocket I/O loop
func (c *Cmd) runIO(adapter *Adapter) {
	defer adapter.Close()
	defer c.conn.Close()

	ctx, cancel := context.WithCancel(c.ctx)
	c.cancel = cancel // Store cancel function for Close() method
	defer cancel()

	// If PTY is active, give it the context to manage lifecycle
	if c.ptyMaster != nil {
		c.setupPTYContext(ctx, cancel)
		// PTY handles its own I/O, we just wait for completion
		<-c.ptyMaster.closed
		return
	}

	// For non-PTY mode, handle I/O with channels
	type wsMessage struct {
		msg *Message
		err error
	}

	// Channel for incoming WebSocket messages
	msgChan := make(chan wsMessage, 1)

	// Start WebSocket reader
	go func() {
		for {
			msg, err := adapter.ReadMessage()
			select {
			case msgChan <- wsMessage{msg, err}:
			case <-ctx.Done():
				return
			}
			if err != nil {
				return
			}
		}
	}()

	// Send EOF if no stdin
	if c.Stdin == nil {
		adapter.WriteStdinEOF()
	}

	// Channels for stdin and ping ticker
	stdinChan := make(chan []byte, 1)
	if c.Stdin != nil {
		go func() {
			buf := make([]byte, 4096)
			for {
				n, err := c.Stdin.Read(buf)
				if n > 0 {
					data := make([]byte, n)
					copy(data, buf[:n])
					select {
					case stdinChan <- data:
					case <-ctx.Done():
						return
					}
				}
				if err != nil {
					if err == io.EOF {
						adapter.WriteStdinEOF()
					}
					close(stdinChan)
					return
				}
			}
		}()
	}

	// Ping ticker
	pingInterval := c.PingInterval
	if pingInterval == 0 {
		pingInterval = 5 * time.Second
	}
	pingTicker := time.NewTicker(pingInterval)
	defer pingTicker.Stop()

	// Get output writers
	stdout := c.Stdout
	stderr := c.Stderr
	if stdout == nil {
		stdout = os.Stdout
	}
	if stderr == nil {
		stderr = os.Stderr
	}

	// Main event loop
	for {
		select {
		case <-ctx.Done():
			return

		case data := <-stdinChan:
			if data != nil {
				if err := adapter.WriteStdin(data); err != nil {
					return
				}
			}

		case wsMsg := <-msgChan:
			if wsMsg.err != nil {
				// Check for normal close
				if !gorillaws.IsCloseError(wsMsg.err, gorillaws.CloseNormalClosure, gorillaws.CloseGoingAway) {
					// Unexpected error, but continue to try to get exit code
					continue
				}
				return
			}

			switch wsMsg.msg.Type {
			case MessageTypeStdout:
				if _, err := stdout.Write(wsMsg.msg.Data); err != nil {
					return
				}
			case MessageTypeStderr:
				if _, err := stderr.Write(wsMsg.msg.Data); err != nil {
					return
				}
			case MessageTypeExit:
				code, _ := DecodeExit(wsMsg.msg.Data)
				// Send exit code
				select {
				case c.exitChan <- code:
				default:
				}
				// Normal exit - just return, deferred cleanup will handle the rest
				return
			case MessageTypeError:
				// Server error
				return
			}

		case <-pingTicker.C:
			if err := adapter.WritePing(); err != nil {
				return
			}
		}
	}
}

// ExitCode returns the exit code of the process
// Returns -1 if the process hasn't exited or if the exit code is unknown
func (c *Cmd) ExitCode() int {
	select {
	case code := <-c.exitChan:
		// Put it back for other callers
		select {
		case c.exitChan <- code:
		default:
		}
		return code
	default:
		return -1
	}
}

// getAdapter returns the WebSocket adapter (for PTY support)
func (c *Cmd) getAdapter() *Adapter {
	select {
	case adapter := <-c.adapterChan:
		// Put it back for other callers
		select {
		case c.adapterChan <- adapter:
		default:
		}
		return adapter
	default:
		return nil
	}
}

// setupPTYContext sets up the context for PTY to manage command lifecycle
func (c *Cmd) setupPTYContext(ctx context.Context, cancel context.CancelFunc) {
	if c.ptyMaster != nil {
		c.ptyMaster.ctx = ctx
		c.ptyMaster.cancel = cancel
	}
}

// Close gracefully shuts down the command and all its goroutines
func (c *Cmd) Close() error {
	// Cancel the context to stop all goroutines
	if c.cancel != nil {
		c.cancel()
	}

	// Close WebSocket connection if open
	if c.conn != nil {
		// Send close message
		deadline := time.Now().Add(time.Second)
		c.conn.SetWriteDeadline(deadline)
		c.conn.WriteControl(gorillaws.CloseMessage,
			gorillaws.FormatCloseMessage(gorillaws.CloseNormalClosure, ""),
			deadline)
		c.conn.Close()
	}

	// Close PTY if active
	if c.ptyMaster != nil {
		c.ptyMaster.Close()
	}

	return nil
}

// Resize sends a terminal resize message
func (c *Cmd) Resize(width, height uint16) error {
	// If we have a PTY, use its SetSize method
	if c.ptyMaster != nil {
		return c.ptyMaster.SetSize(height, width)
	}

	// Otherwise, send resize message directly
	adapter := c.getAdapter()
	if adapter == nil {
		return fmt.Errorf("no active connection")
	}

	return adapter.WriteResize(height, width)
}
