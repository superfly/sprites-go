package wsexec

import (
	"encoding/json"
	"errors"
	"io"

	gorillaws "github.com/gorilla/websocket"
)

// StreamID represents the stream identifier for non-PTY mode
type StreamID byte

const (
	StreamStdin    StreamID = 0x00
	StreamStdout   StreamID = 0x01
	StreamStderr   StreamID = 0x02
	StreamExit     StreamID = 0x03
	StreamStdinEOF StreamID = 0x04 // Explicit EOF signal
)

// ControlMessage represents a control message sent via text WebSocket frames
type ControlMessage struct {
	Type string `json:"type"`
	// Resize fields
	Cols uint16 `json:"cols,omitempty"`
	Rows uint16 `json:"rows,omitempty"`
}

// Adapter wraps a gorilla WebSocket connection for our simplified protocol
type Adapter struct {
	conn      *gorillaws.Conn
	isPTY     bool // Whether this is a PTY session (transparent byte mode)
	writeChan chan writeRequest
	done      chan struct{}
}

type writeRequest struct {
	messageType int
	data        []byte
	result      chan error
}

// NewAdapter creates a new WebSocket adapter
func NewAdapter(conn *gorillaws.Conn, isPTY bool) *Adapter {
	a := &Adapter{
		conn:      conn,
		isPTY:     isPTY,
		writeChan: make(chan writeRequest, 100),
		done:      make(chan struct{}),
	}

	// Start the write loop
	go a.writeLoop()

	return a
}

// writeLoop handles all writes to ensure only one goroutine writes at a time
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

// WriteRaw writes raw bytes directly to the WebSocket (for PTY mode)
func (a *Adapter) WriteRaw(data []byte) error {
	result := make(chan error, 1)
	select {
	case a.writeChan <- writeRequest{
		messageType: gorillaws.BinaryMessage,
		data:        data,
		result:      result,
	}:
		return <-result
	case <-a.done:
		return errors.New("adapter closed")
	}
}

// WriteControl writes a control message as a text WebSocket frame
func (a *Adapter) WriteControl(msg *ControlMessage) error {
	data, err := json.Marshal(msg)
	if err != nil {
		return err
	}

	result := make(chan error, 1)
	select {
	case a.writeChan <- writeRequest{
		messageType: gorillaws.TextMessage,
		data:        data,
		result:      result,
	}:
		return <-result
	case <-a.done:
		return errors.New("adapter closed")
	}
}

// WriteStream writes data with a stream ID prefix (for non-PTY mode)
func (a *Adapter) WriteStream(stream StreamID, data []byte) error {
	if a.isPTY {
		// In PTY mode, just write raw data
		return a.WriteRaw(data)
	}

	// Prepend stream ID to data
	msg := make([]byte, len(data)+1)
	msg[0] = byte(stream)
	copy(msg[1:], data)

	return a.WriteRaw(msg)
}

// WriteExit writes an exit code message
func (a *Adapter) WriteExit(code int) error {
	if code < 0 || code > 255 {
		code = 255 // Cap at 255 for byte representation
	}
	return a.WriteStream(StreamExit, []byte{byte(code)})
}

// ReadRaw reads raw bytes from the WebSocket
func (a *Adapter) ReadRaw() ([]byte, error) {
	messageType, data, err := a.conn.ReadMessage()
	if err != nil {
		return nil, err
	}

	// We only handle binary messages
	if messageType != gorillaws.BinaryMessage {
		return nil, errors.New("invalid message type: only binary messages are supported")
	}

	return data, nil
}

// ReadStream reads a message and extracts the stream ID (for non-PTY mode)
func (a *Adapter) ReadStream() (StreamID, []byte, error) {
	data, err := a.ReadRaw()
	if err != nil {
		return 0, nil, err
	}

	if a.isPTY {
		// In PTY mode, all data is stdin
		return StreamStdin, data, nil
	}

	if len(data) == 0 {
		return 0, nil, errors.New("empty message")
	}

	stream := StreamID(data[0])

	return stream, data[1:], nil
}

// Close closes the WebSocket connection
func (a *Adapter) Close() error {
	close(a.done)
	return a.conn.Close()
}

// Read implements io.Reader for PTY mode (raw bytes)
func (a *Adapter) Read(p []byte) (n int, err error) {
	if !a.isPTY {
		return 0, errors.New("Read only supported in PTY mode")
	}
	data, err := a.ReadRaw()
	if err != nil {
		return 0, err
	}
	n = copy(p, data)
	return n, nil
}

// Write implements io.Writer for PTY mode (raw bytes)
func (a *Adapter) Write(p []byte) (n int, err error) {
	if !a.isPTY {
		return 0, errors.New("Write only supported in PTY mode")
	}
	err = a.WriteRaw(p)
	if err != nil {
		return 0, err
	}
	return len(p), nil
}

// streamReader reads from WebSocket for a specific stream
type streamReader struct {
	ws       *Adapter
	streamID StreamID
	buffer   []byte // Buffer for unread data
}

func (r *streamReader) Read(p []byte) (n int, err error) {
	// If we have buffered data, return it first
	if len(r.buffer) > 0 {
		n = copy(p, r.buffer)
		r.buffer = r.buffer[n:]
		return n, nil
	}

	// Read new messages
	for {
		stream, data, err := r.ws.ReadStream()
		if err != nil {
			return 0, err
		}

		// Handle explicit EOF message
		if stream == StreamStdinEOF {
			return 0, io.EOF
		}

		// Only read data for our stream
		if stream == r.streamID {
			n = copy(p, data)
			// If we couldn't fit all data, buffer the rest
			if n < len(data) {
				r.buffer = data[n:]
			}
			return n, nil
		}
		// Ignore data for other streams and keep reading
	}
}

// streamWriter writes to WebSocket with a specific stream ID
type streamWriter struct {
	ws       *Adapter
	streamID StreamID
}

func (w *streamWriter) Write(p []byte) (n int, err error) {
	err = w.ws.WriteStream(w.streamID, p)
	if err != nil {
		return 0, err
	}
	return len(p), nil
}
