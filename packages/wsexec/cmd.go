package wsexec

import (
	"context"
	"crypto/tls"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"os"
	"strings"
	"time"

	gorillaws "github.com/gorilla/websocket"
)

// BrowserOpenEvent contains the parsed browser open request
type BrowserOpenEvent struct {
	URL   string
	Ports []string
}

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

// BrowserOpenFunc is a function that handles browser open requests
type BrowserOpenFunc func(url string, ports []string)

// TextMessageHandler is a function that handles arbitrary text messages from the server
type TextMessageHandler func(data []byte)

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

	// Browser open handler
	BrowserOpen BrowserOpenFunc

	// Text message handler for arbitrary server messages
	TextMessageHandler TextMessageHandler

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

	// Gracefully close the connection when the I/O loop finishes
	defer c.Close()

	// Get output writers
	stdout := c.Stdout
	stderr := c.Stderr
	if stdout == nil {
		stdout = os.Stdout
	}
	if stderr == nil {
		stderr = os.Stderr
	}

	// For PTY mode, handle messages directly for text message support
	if c.Tty {
		// Copy stdin to WebSocket
		if c.Stdin != nil {
			go io.Copy(adapter, c.Stdin)
		}

		// Set up output writer with optional OSC monitoring
		var output io.Writer = stdout
		if c.BrowserOpen != nil {
			oscMonitor := NewOSCMonitor(c.handleOSCSequence)
			output = io.MultiWriter(stdout, oscMonitor)
		}

		// Handle WebSocket messages directly (both binary and text)
		for {
			messageType, data, err := conn.ReadMessage()
			if err != nil {
				// Connection closed
				break
			}

			switch messageType {
			case gorillaws.BinaryMessage:
				// Write binary data to output
				output.Write(data)
			case gorillaws.TextMessage:
				// Handle text messages
				c.handleTextMessage(data)
			}
		}

		// When message loop exits, the command is done
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

	// Handle WebSocket messages directly for text message support
	for {
		messageType, data, err := conn.ReadMessage()
		if err != nil {
			// Connection closed
			return
		}

		switch messageType {
		case gorillaws.BinaryMessage:
			// Handle binary messages with stream multiplexing
			if len(data) == 0 {
				continue
			}
			stream := StreamID(data[0])
			payload := data[1:]

			switch stream {
			case StreamStdout:
				stdout.Write(payload)
			case StreamStderr:
				stderr.Write(payload)
			case StreamExit:
				if len(payload) > 0 {
					code := int(payload[0])
					select {
					case c.exitChan <- code:
					default:
					}
				}
				return // Command finished
			}
		case gorillaws.TextMessage:
			// Handle text messages
			c.handleTextMessage(data)
		}
	}
}

// handleTextMessage processes text messages from the server
func (c *Cmd) handleTextMessage(data []byte) {
	// First, try to handle as control message (resize)
	var controlMsg ControlMessage
	if err := json.Unmarshal(data, &controlMsg); err == nil && controlMsg.Type == "resize" {
		// Resize messages are handled internally by wsexec
		// (though typically these come from client to server, not server to client)
		return
	}

	// If we have a text message handler, call it for arbitrary messages
	if c.TextMessageHandler != nil {
		c.TextMessageHandler(data)
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

// handleOSCSequence handles OSC escape sequences
func (c *Cmd) handleOSCSequence(sequence string) {
	// Parse OSC 9999 sequences for browser-open
	// Format: 9999;browser-open;URL;ports (ports is comma-separated list)
	parts := strings.Split(sequence, ";")
	if len(parts) >= 3 && parts[0] == "9999" && parts[1] == "browser-open" && c.BrowserOpen != nil {
		url := parts[2]
		var ports []string

		// Parse ports if present (fourth part)
		if len(parts) >= 4 && parts[3] != "" {
			ports = strings.Split(parts[3], ",")
			// Clean up any empty strings
			var cleanPorts []string
			for _, port := range ports {
				if trimmed := strings.TrimSpace(port); trimmed != "" {
					cleanPorts = append(cleanPorts, trimmed)
				}
			}
			ports = cleanPorts
		}

		c.BrowserOpen(url, ports)
	}
}
