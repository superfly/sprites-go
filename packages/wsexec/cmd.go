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
		Request:   req,
		Path:      name,
		Args:      append([]string{name}, arg...),
		ctx:       context.Background(),
		startChan: make(chan error, 1),
		exitChan:  make(chan int, 1),
		doneChan:  make(chan struct{}),
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

	// Private fields
	ctx     context.Context
	conn    *gorillaws.Conn
	adapter *Adapter

	// Channels for communication
	startChan chan error    // Signals start completion
	exitChan  chan int      // Sends exit code
	doneChan  chan struct{} // Signals command completion
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
	defer close(c.doneChan)

	// Set up WebSocket dialer
	dialer := gorillaws.DefaultDialer
	dialer.HandshakeTimeout = 10 * time.Second
	dialer.ReadBufferSize = 1024 * 1024  // 1MB buffer
	dialer.WriteBufferSize = 1024 * 1024 // 1MB buffer

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
	c.adapter = NewAdapter(conn, c.Tty)

	// Signal successful start
	c.startChan <- nil

	// Run the I/O loop
	c.runIO()
}

// Wait waits for the command to exit
func (c *Cmd) Wait() error {
	select {
	case <-c.doneChan:
		return nil
	case <-c.ctx.Done():
		return c.ctx.Err()
	}
}

// runIO handles the WebSocket I/O loop
func (c *Cmd) runIO() {
	adapter := c.adapter
	conn := c.conn

	if adapter == nil || conn == nil {
		return
	}

	defer adapter.Close()
	defer conn.Close()

	// Get output writers
	stdout := c.Stdout
	stderr := c.Stderr
	if stdout == nil {
		stdout = os.Stdout
	}
	if stderr == nil {
		stderr = os.Stderr
	}

	// For PTY mode, it's just bidirectional copying
	if c.Tty {
		// Copy stdin to WebSocket
		if c.Stdin != nil {
			go io.Copy(adapter, c.Stdin)
		}

		// Copy WebSocket to stdout
		io.Copy(stdout, adapter)

		// When io.Copy returns, the command is done
		// Send default exit code
		select {
		case c.exitChan <- 0:
		default:
		}
		return
	}

	// For non-PTY mode, we need to handle stream multiplexing
	// Copy stdin to WebSocket in background
	if c.Stdin != nil {
		go func() {
			stdinWriter := &streamWriter{ws: adapter, streamID: StreamStdin}
			io.Copy(stdinWriter, c.Stdin)

			// Send explicit EOF message
			adapter.WriteStream(StreamStdinEOF, []byte{})
		}()
	}

	// Read messages until we get an exit code
	for {
		stream, data, err := adapter.ReadStream()
		if err != nil {
			// Connection closed
			return
		}

		switch stream {
		case StreamStdout:
			stdout.Write(data)
		case StreamStderr:
			stderr.Write(data)
		case StreamExit:
			if len(data) > 0 {
				code := int(data[0])
				select {
				case c.exitChan <- code:
				default:
				}
			}
			return // Command finished
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
		// Check if done
		if c.IsDone() {
			return 0 // Default to success if done but no exit code
		}
		return -1
	}
}

// IsDone returns true if the command has finished
func (c *Cmd) IsDone() bool {
	select {
	case <-c.doneChan:
		return true
	default:
		return false
	}
}

// Close gracefully shuts down the command and all its goroutines
func (c *Cmd) Close() error {
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

	return nil
}

// Resize sends a terminal resize message (for PTY mode)
func (c *Cmd) Resize(width, height uint16) error {
	if !c.Tty || c.adapter == nil {
		return nil
	}

	// Send resize control message via text frame
	msg := &ControlMessage{
		Type: "resize",
		Cols: width,
		Rows: height,
	}

	return c.adapter.WriteControl(msg)
}
