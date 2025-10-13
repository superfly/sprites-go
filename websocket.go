package sprites

import (
	"context"
	"crypto/tls"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net/http"
	"os"
	"time"

	"github.com/gorilla/websocket"
	"golang.org/x/term"
)

// StreamID represents different stream types in the protocol
type StreamID byte

const (
	StreamStdin    StreamID = 0
	StreamStdout   StreamID = 1
	StreamStderr   StreamID = 2
	StreamExit     StreamID = 3
	StreamStdinEOF StreamID = 4
)

// ControlMessage represents control messages sent over the WebSocket
type ControlMessage struct {
	Type string `json:"type"`
	Cols uint16 `json:"cols,omitempty"`
	Rows uint16 `json:"rows,omitempty"`
}

// wsCmd represents a remote command execution via WebSocket
type wsCmd struct {
	Path           string
	Args           []string
	Request        *http.Request
	Stdin          io.Reader
	Stdout, Stderr io.Writer
	Env            []string
	Dir            string
	Tty            bool

	ctx       context.Context
	conn      *websocket.Conn
	adapter   *wsAdapter
	startChan chan error
	exitChan  chan int
	doneChan  chan struct{}

	// TextMessageHandler is called when text messages are received over the WebSocket
	TextMessageHandler func([]byte)

	// existingConn allows reusing an existing WebSocket connection (for control connections)
	existingConn *websocket.Conn
	// usingControl indicates if this is using a control connection
	usingControl bool
}

// wsAdapter wraps a WebSocket connection for terminal communication
type wsAdapter struct {
	conn      *websocket.Conn
	isPTY     bool
	writeChan chan writeRequest
	done      chan struct{}
}

// writeRequest represents a pending write to the WebSocket
type writeRequest struct {
	messageType int
	data        []byte
	result      chan error
}

// newWSCmd creates a new WebSocket command
func newWSCmd(req *http.Request, name string, arg ...string) *wsCmd {
	if req == nil {
		panic("sprites: newWSCmd called with nil request")
	}
	return &wsCmd{
		Path:      name,
		Args:      append([]string{name}, arg...),
		Request:   req,
		ctx:       context.Background(),
		startChan: make(chan error, 1),
		exitChan:  make(chan int, 1),
		doneChan:  make(chan struct{}),
	}
}

// newWSCmdContext is like newWSCmd but includes a context
func newWSCmdContext(ctx context.Context, req *http.Request, name string, arg ...string) *wsCmd {
	if ctx == nil {
		panic("sprites: newWSCmdContext called with nil context")
	}
	c := newWSCmd(req, name, arg...)
	c.ctx = ctx
	return c
}

// Run starts the command and waits for it to complete
func (c *wsCmd) Run() error {
	if err := c.Start(); err != nil {
		return err
	}
	return c.Wait()
}

// Start begins the WebSocket connection and I/O loop
func (c *wsCmd) Start() error {
	go c.start()
	select {
	case err := <-c.startChan:
		return err
	case <-c.ctx.Done():
		return c.ctx.Err()
	}
}

func (c *wsCmd) start() {
	defer close(c.doneChan)

	var conn *websocket.Conn
	var err error

	// Use existing connection if provided (for control connections)
	if c.existingConn != nil {
		conn = c.existingConn

		// Send operation start message for control connections
		if c.usingControl {
			startMsg := map[string]interface{}{
				"type":      "start",
				"operation": "exec",
				"params": map[string]interface{}{
					"path":       c.Path,
					"args":       c.Args,
					"env":        c.Env,
					"dir":        c.Dir,
					"tty":        c.Tty,
					"stdin":      c.Stdin != nil,
					"keep_alive": true,
				},
			}
			if err := conn.WriteJSON(&startMsg); err != nil {
				c.startChan <- fmt.Errorf("failed to send operation start message: %w", err)
				return
			}
		}
	} else {
		// Dial new connection (legacy direct WebSocket path)
		dialer := websocket.DefaultDialer
		dialer.HandshakeTimeout = 10 * time.Second
		dialer.ReadBufferSize = 1024 * 1024
		dialer.WriteBufferSize = 1024 * 1024

		if c.Request.URL.Scheme == "wss" {
			dialer.TLSClientConfig = &tls.Config{}
		}
		conn, resp, err := dialer.DialContext(c.ctx, c.Request.URL.String(), c.Request.Header)
		if err != nil {
			errMsg := fmt.Sprintf("failed to connect: %v", err)
			if resp != nil {
				body, readErr := io.ReadAll(resp.Body)
				resp.Body.Close()
				if readErr == nil && len(body) > 0 {
					errMsg = fmt.Sprintf("failed to connect: %v (HTTP %d: %s)", err, resp.StatusCode, string(body))
				} else if readErr == nil {
					errMsg = fmt.Sprintf("failed to connect: %v (HTTP %d)", err, resp.StatusCode)
				}
			}
			c.startChan <- fmt.Errorf("%s", errMsg)
			return
		}
	}

	c.conn = conn
	c.adapter = newWSAdapter(conn, c.Tty)

	// Send initial resize message for TTY mode
	if c.Tty {
		go func() {
			time.Sleep(10 * time.Millisecond)
			if term.IsTerminal(int(os.Stdin.Fd())) {
				if width, height, err := term.GetSize(int(os.Stdin.Fd())); err == nil {
					c.Resize(uint16(width), uint16(height))
				}
			}
		}()
	}

	c.startChan <- nil
	c.runIO()
}

// Wait waits for the command to finish
func (c *wsCmd) Wait() error {
	select {
	case <-c.doneChan:
		return nil
	case <-c.ctx.Done():
		return c.ctx.Err()
	}
}

func (c *wsCmd) runIO() {
	adapter := c.adapter
	conn := c.conn
	if adapter == nil || conn == nil {
		return
	}
	defer c.Close()

	stdout := c.Stdout
	stderr := c.Stderr
	if stdout == nil {
		stdout = os.Stdout
	}
	if stderr == nil {
		stderr = os.Stderr
	}

	if c.Tty {
		// PTY mode - handle raw I/O
		if c.Stdin != nil {
			go io.Copy(adapter, c.Stdin)
		}

		for {
			messageType, data, err := conn.ReadMessage()
			if err != nil {
				adapter.Close()
				if c.ctx.Err() != nil {
					select {
					case c.exitChan <- 1:
					default:
					}
					return
				}
				if closeErr, ok := err.(*websocket.CloseError); ok && closeErr.Code == websocket.CloseNormalClosure {
					select {
					case c.exitChan <- 0:
					default:
					}
				} else {
					select {
					case c.exitChan <- 1:
					default:
					}
				}
				return
			}
			switch messageType {
			case websocket.BinaryMessage:
				stdout.Write(data)
			case websocket.TextMessage:
				// Handle control messages
				if c.TextMessageHandler != nil {
					c.TextMessageHandler(data)
				}
			}
		}
	}

	// Non-PTY mode - handle stream-based I/O
	if c.Stdin != nil {
		go func() {
			stdinWriter := &streamWriter{ws: adapter, streamID: StreamStdin}
			io.Copy(stdinWriter, c.Stdin)
			adapter.WriteStream(StreamStdinEOF, []byte{})
		}()
	} else {
		// Send EOF immediately if no stdin is provided
		go func() {
			adapter.WriteStream(StreamStdinEOF, []byte{})
		}()
	}

	for {
		messageType, data, err := conn.ReadMessage()
		if err != nil {
			adapter.Close()
			return
		}
		switch messageType {
		case websocket.BinaryMessage:
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
				adapter.Close()
				return
			}
		case websocket.TextMessage:
			// Handle control messages
			if c.TextMessageHandler != nil {
				c.TextMessageHandler(data)
			}
		}
	}
}

// ExitCode returns the exit code, or -1 if unknown
func (c *wsCmd) ExitCode() int {
	select {
	case code := <-c.exitChan:
		select {
		case c.exitChan <- code:
		default:
		}
		return code
	default:
		if c.IsDone() {
			return 0
		}
		return -1
	}
}

// IsDone reports whether the command has finished
func (c *wsCmd) IsDone() bool {
	select {
	case <-c.doneChan:
		return true
	default:
		return false
	}
}

// Close gracefully closes the WebSocket connection
func (c *wsCmd) Close() error {
	if c.conn != nil {
		deadline := time.Now().Add(time.Second)
		c.conn.SetWriteDeadline(deadline)
		c.conn.WriteControl(websocket.CloseMessage,
			websocket.FormatCloseMessage(websocket.CloseNormalClosure, ""),
			deadline)
		c.conn.Close()
	}
	return nil
}

// Resize sends a resize control message (PTY mode)
func (c *wsCmd) Resize(width, height uint16) error {
	if !c.Tty || c.adapter == nil {
		return nil
	}
	msg := &ControlMessage{Type: "resize", Cols: width, Rows: height}
	return c.adapter.WriteControl(msg)
}

// newWSAdapter creates a new WebSocket adapter
func newWSAdapter(conn *websocket.Conn, isPTY bool) *wsAdapter {
	a := &wsAdapter{
		conn:      conn,
		isPTY:     isPTY,
		writeChan: make(chan writeRequest, 100),
		done:      make(chan struct{}),
	}
	go a.writeLoop()
	return a
}

func (a *wsAdapter) writeLoop() {
	for {
		select {
		case req := <-a.writeChan:
			err := a.conn.WriteMessage(req.messageType, req.data)
			if req.result != nil {
				req.result <- err
			}
		case <-a.done:
			return
		}
	}
}

// WriteRaw writes raw bytes to the WebSocket
func (a *wsAdapter) WriteRaw(data []byte) error {
	result := make(chan error, 1)
	select {
	case a.writeChan <- writeRequest{messageType: websocket.BinaryMessage, data: data, result: result}:
		return <-result
	case <-a.done:
		return errors.New("adapter closed")
	}
}

// WriteControl sends a control message as a JSON text frame
func (a *wsAdapter) WriteControl(msg *ControlMessage) error {
	data, err := json.Marshal(msg)
	if err != nil {
		return err
	}
	result := make(chan error, 1)
	select {
	case a.writeChan <- writeRequest{messageType: websocket.TextMessage, data: data, result: result}:
		return <-result
	case <-a.done:
		return errors.New("adapter closed")
	}
}

// WriteStream writes data with a stream ID prefix (non-PTY mode)
func (a *wsAdapter) WriteStream(stream StreamID, data []byte) error {
	if a.isPTY {
		return a.WriteRaw(data)
	}
	msg := make([]byte, len(data)+1)
	msg[0] = byte(stream)
	copy(msg[1:], data)
	return a.WriteRaw(msg)
}

// Write implements io.Writer for PTY mode
func (a *wsAdapter) Write(p []byte) (int, error) {
	if !a.isPTY {
		return 0, errors.New("Write only supported in PTY mode")
	}
	err := a.WriteRaw(p)
	if err != nil {
		return 0, err
	}
	return len(p), nil
}

// Close shuts down the write loop and WebSocket connection
func (a *wsAdapter) Close() error {
	close(a.done)
	return a.conn.Close()
}

// streamWriter writes to a specific stream via the adapter
type streamWriter struct {
	ws       *wsAdapter
	streamID StreamID
}

func (w *streamWriter) Write(p []byte) (int, error) {
	err := w.ws.WriteStream(w.streamID, p)
	if err != nil {
		return 0, err
	}
	return len(p), nil
}
