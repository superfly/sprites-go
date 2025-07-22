package terminal

import (
	"context"
	"crypto/tls"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net/http"
	"os"
	"strings"
	"time"

	gorillaws "github.com/gorilla/websocket"
)

// Adapter wraps a gorilla WebSocket connection for client-side terminal communication.
type Adapter struct {
	conn      *gorillaws.Conn
	isPTY     bool
	writeChan chan clientWriteRequest
	done      chan struct{}
}

// clientWriteRequest represents a pending write to the WebSocket for client adapter.
type clientWriteRequest struct {
	messageType int
	data        []byte
	result      chan error
}

// NewAdapter creates a new WebSocket adapter for client-side terminal communication.
func NewAdapter(conn *gorillaws.Conn, isPTY bool) *Adapter {
	a := &Adapter{
		conn:      conn,
		isPTY:     isPTY,
		writeChan: make(chan clientWriteRequest, 100),
		done:      make(chan struct{}),
	}
	go a.writeLoop()
	return a
}

func (a *Adapter) writeLoop() {
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

// WriteRaw writes raw bytes to the WebSocket.
func (a *Adapter) WriteRaw(data []byte) error {
	result := make(chan error, 1)
	select {
	case a.writeChan <- clientWriteRequest{messageType: gorillaws.BinaryMessage, data: data, result: result}:
		return <-result
	case <-a.done:
		return errors.New("adapter closed")
	}
}

// WriteControl sends a control message (e.g. resize) as a JSON text frame.
func (a *Adapter) WriteControl(msg *ControlMessage) error {
	data, err := json.Marshal(msg)
	if err != nil {
		return err
	}
	result := make(chan error, 1)
	select {
	case a.writeChan <- clientWriteRequest{messageType: gorillaws.TextMessage, data: data, result: result}:
		return <-result
	case <-a.done:
		return errors.New("adapter closed")
	}
}

// WriteStream writes data with a stream ID prefix (non-PTY mode).
func (a *Adapter) WriteStream(stream StreamID, data []byte) error {
	if a.isPTY {
		return a.WriteRaw(data)
	}
	msg := make([]byte, len(data)+1)
	msg[0] = byte(stream)
	copy(msg[1:], data)
	return a.WriteRaw(msg)
}

// WriteExit writes an exit code frame.
func (a *Adapter) WriteExit(code int) error {
	if code < 0 || code > 255 {
		code = 255
	}
	return a.WriteStream(StreamExit, []byte{byte(code)})
}

// ReadRaw reads the next binary frame from WebSocket.
func (a *Adapter) ReadRaw() ([]byte, error) {
	messageType, data, err := a.conn.ReadMessage()
	if err != nil {
		return nil, err
	}
	if messageType != gorillaws.BinaryMessage {
		return nil, errors.New("invalid message type: only binary messages are supported")
	}
	return data, nil
}

// ReadStream reads from the WebSocket and extracts the stream ID and payload.
func (a *Adapter) ReadStream() (StreamID, []byte, error) {
	data, err := a.ReadRaw()
	if err != nil {
		return 0, nil, err
	}
	if a.isPTY {
		return StreamStdin, data, nil
	}
	if len(data) == 0 {
		return 0, nil, errors.New("empty message")
	}
	stream := StreamID(data[0])
	return stream, data[1:], nil
}

// Close shuts down the write loop and WebSocket connection.
func (a *Adapter) Close() error {
	close(a.done)
	return a.conn.Close()
}

// Read implements io.Reader for PTY mode (raw bytes).
func (a *Adapter) Read(p []byte) (int, error) {
	if !a.isPTY {
		return 0, errors.New("Read only supported in PTY mode")
	}
	data, err := a.ReadRaw()
	if err != nil {
		return 0, err
	}
	n := copy(p, data)
	return n, nil
}

// Write implements io.Writer for PTY mode (raw bytes).
func (a *Adapter) Write(p []byte) (int, error) {
	if !a.isPTY {
		return 0, errors.New("Write only supported in PTY mode")
	}
	err := a.WriteRaw(p)
	if err != nil {
		return 0, err
	}
	return len(p), nil
}

// streamReader reads from a specific stream via the Adapter.
type streamReader struct {
	ws       *Adapter
	streamID StreamID
	buffer   []byte
}

func (r *streamReader) Read(p []byte) (int, error) {
	if len(r.buffer) > 0 {
		n := copy(p, r.buffer)
		r.buffer = r.buffer[n:]
		return n, nil
	}
	for {
		stream, data, err := r.ws.ReadStream()
		if err != nil {
			return 0, err
		}
		if stream == StreamStdinEOF {
			return 0, io.EOF
		}
		if stream == r.streamID {
			n := copy(p, data)
			if n < len(data) {
				r.buffer = data[n:]
			}
			return n, nil
		}
	}
}

// streamWriter writes to a specific stream via the Adapter.
type streamWriter struct {
	ws       *Adapter
	streamID StreamID
}

func (w *streamWriter) Write(p []byte) (int, error) {
	err := w.ws.WriteStream(w.streamID, p)
	if err != nil {
		return 0, err
	}
	return len(p), nil
}

// Cmd represents a remote command execution via WebSocket.
type Cmd struct {
	Path               string
	Args               []string
	Request            *http.Request
	Stdin              io.Reader
	Stdout, Stderr     io.Writer
	Env                []string
	Dir                string
	Tty                bool
	BrowserOpen        func(string, []string)
	TextMessageHandler func(data []byte)

	ctx       context.Context
	conn      *gorillaws.Conn
	adapter   *Adapter
	startChan chan error
	exitChan  chan int
	doneChan  chan struct{}
}

// Command returns a new Cmd for executing remotely via WebSocket.
func Command(req *http.Request, name string, arg ...string) *Cmd {
	if req == nil {
		panic("terminal: Command called with nil request")
	}
	return &Cmd{
		Path:      name,
		Args:      append([]string{name}, arg...),
		Request:   req,
		ctx:       context.Background(),
		startChan: make(chan error, 1),
		exitChan:  make(chan int, 1),
		doneChan:  make(chan struct{}),
	}
}

// CommandContext is like Command but includes a context.
func CommandContext(ctx context.Context, req *http.Request, name string, arg ...string) *Cmd {
	if ctx == nil {
		panic("terminal: CommandContext called with nil context")
	}
	c := Command(req, name, arg...)
	c.ctx = ctx
	return c
}

// Run starts the command and waits for it to complete.
func (c *Cmd) Run() error {
	if err := c.Start(); err != nil {
		return err
	}
	return c.Wait()
}

// Start begins the WebSocket connection and I/O loop.
func (c *Cmd) Start() error {
	go c.start()
	select {
	case err := <-c.startChan:
		return err
	case <-c.ctx.Done():
		return c.ctx.Err()
	}
}

func (c *Cmd) start() {
	defer close(c.doneChan)
	dialer := gorillaws.DefaultDialer
	dialer.HandshakeTimeout = 10 * time.Second
	dialer.ReadBufferSize = 1024 * 1024
	dialer.WriteBufferSize = 1024 * 1024

	if c.Request.URL.Scheme == "wss" {
		dialer.TLSClientConfig = &tls.Config{}
	}
	conn, resp, err := dialer.DialContext(c.ctx, c.Request.URL.String(), c.Request.Header)
	if err != nil {
		// If we have a response, try to read the body to help with debugging
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
		c.startChan <- fmt.Errorf(errMsg)
		return
	}
	c.conn = conn
	c.adapter = NewAdapter(conn, c.Tty)
	c.startChan <- nil
	c.runIO()
}

// Wait waits for the command to finish.
func (c *Cmd) Wait() error {
	select {
	case <-c.doneChan:
		return nil
	case <-c.ctx.Done():
		return c.ctx.Err()
	}
}

func (c *Cmd) runIO() {
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
		if c.Stdin != nil {
			go io.Copy(adapter, c.Stdin)
		}
		var output io.Writer = stdout
		if c.BrowserOpen != nil {
			oscMonitor := NewOSCMonitor(c.handleOSCSequence)
			output = io.MultiWriter(stdout, oscMonitor)
		}
		for {
			messageType, data, err := conn.ReadMessage()
			if err != nil {
				break
			}
			switch messageType {
			case gorillaws.BinaryMessage:
				output.Write(data)
			case gorillaws.TextMessage:
				c.handleTextMessage(data)
			}
		}
		select {
		case c.exitChan <- 0:
		default:
		}
		return
	}

	if c.Stdin != nil {
		go func() {
			stdinWriter := &streamWriter{ws: adapter, streamID: StreamStdin}
			io.Copy(stdinWriter, c.Stdin)
			adapter.WriteStream(StreamStdinEOF, []byte{})
		}()
	}

	for {
		messageType, data, err := conn.ReadMessage()
		if err != nil {
			return
		}
		switch messageType {
		case gorillaws.BinaryMessage:
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
				return
			}
		case gorillaws.TextMessage:
			c.handleTextMessage(data)
		}
	}
}

func (c *Cmd) handleTextMessage(data []byte) {
	var controlMsg ControlMessage
	if err := json.Unmarshal(data, &controlMsg); err == nil && controlMsg.Type == "resize" {
		return
	}
	if c.TextMessageHandler != nil {
		c.TextMessageHandler(data)
	}
}

// ExitCode returns the exit code, or -1 if unknown.
func (c *Cmd) ExitCode() int {
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

// IsDone reports whether the command has finished.
func (c *Cmd) IsDone() bool {
	select {
	case <-c.doneChan:
		return true
	default:
		return false
	}
}

// Close gracefully closes the WebSocket connection.
func (c *Cmd) Close() error {
	if c.conn != nil {
		deadline := time.Now().Add(time.Second)
		c.conn.SetWriteDeadline(deadline)
		c.conn.WriteControl(gorillaws.CloseMessage,
			gorillaws.FormatCloseMessage(gorillaws.CloseNormalClosure, ""),
			deadline)
		c.conn.Close()
	}
	return nil
}

// Resize sends a resize control message (PTY mode).
func (c *Cmd) Resize(width, height uint16) error {
	if !c.Tty || c.adapter == nil {
		return nil
	}
	msg := &ControlMessage{Type: "resize", Cols: width, Rows: height}
	return c.adapter.WriteControl(msg)
}

func (c *Cmd) handleOSCSequence(sequence string) {
	parts := strings.Split(sequence, ";")
	if len(parts) >= 3 && parts[0] == "9999" && parts[1] == "browser-open" && c.BrowserOpen != nil {
		url := parts[2]
		var ports []string
		if len(parts) >= 4 && parts[3] != "" {
			for _, port := range strings.Split(parts[3], ",") {
				if trimmed := strings.TrimSpace(port); trimmed != "" {
					ports = append(ports, trimmed)
				}
			}
		}
		c.BrowserOpen(url, ports)
	}
}
