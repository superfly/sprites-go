package terminal

import (
	"errors"
	"io"
	"net/http"
	"time"

	gorillaws "github.com/gorilla/websocket"
)

// WebSocketHandler wraps a terminal Session to provide WebSocket connectivity.
type WebSocketHandler struct {
	session  *Session
	upgrader gorillaws.Upgrader
}

// NewWebSocketHandler creates a new WebSocket handler for the given session.
func NewWebSocketHandler(session *Session) *WebSocketHandler {
	return &WebSocketHandler{
		session: session,
		upgrader: gorillaws.Upgrader{
			ReadBufferSize:  1024 * 1024, // 1MB buffer
			WriteBufferSize: 1024 * 1024, // 1MB buffer
			CheckOrigin: func(r *http.Request) bool {
				// TODO: Add proper origin checking
				return true
			},
		},
	}
}

// Handle upgrades the HTTP request to WebSocket and runs the terminal session.
func (h *WebSocketHandler) Handle(w http.ResponseWriter, r *http.Request) error {
	// Upgrade to WebSocket
	conn, err := h.upgrader.Upgrade(w, r, nil)
	if err != nil {
		return err
	}
	defer conn.Close()

	// Set read limit
	conn.SetReadLimit(10 * 1024 * 1024)

	// Create WebSocket streams
	wsStreams := newWebSocketStreams(conn, h.session.tty)
	defer wsStreams.Close()

	// Run the session
	ctx := r.Context()
	exitCode, err := h.session.Run(ctx, wsStreams, wsStreams, wsStreams)

	// Give a moment for any remaining output to be sent
	time.Sleep(50 * time.Millisecond)

	// Send exit code
	if err := wsStreams.WriteExit(exitCode); err != nil {
		// Log error but don't fail
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

	return err
}

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

// webSocketStreams implements io.Reader, io.Writer for WebSocket communication
type webSocketStreams struct {
	conn      *gorillaws.Conn
	isPTY     bool
	writeChan chan writeRequest
	done      chan struct{}
	readBuf   []byte // Buffer for partial reads
}

type writeRequest struct {
	messageType int
	data        []byte
	result      chan error
}

// newWebSocketStreams creates a new WebSocket stream handler
func newWebSocketStreams(conn *gorillaws.Conn, isPTY bool) *webSocketStreams {
	ws := &webSocketStreams{
		conn:      conn,
		isPTY:     isPTY,
		writeChan: make(chan writeRequest, 100),
		done:      make(chan struct{}),
	}

	// Start the write loop
	go ws.writeLoop()

	return ws
}

// writeLoop handles all writes to ensure only one goroutine writes at a time
func (ws *webSocketStreams) writeLoop() {
	for {
		select {
		case req := <-ws.writeChan:
			err := ws.conn.WriteMessage(req.messageType, req.data)
			if req.result != nil {
				req.result <- err
			}
		case <-ws.done:
			return
		}
	}
}

// Read implements io.Reader for the WebSocket streams
func (ws *webSocketStreams) Read(p []byte) (n int, err error) {
	// If we have buffered data, return it first
	if len(ws.readBuf) > 0 {
		n = copy(p, ws.readBuf)
		ws.readBuf = ws.readBuf[n:]
		return n, nil
	}

	// Read new message from WebSocket
	messageType, data, err := ws.conn.ReadMessage()
	if err != nil {
		return 0, err
	}

	// Handle different message types
	switch messageType {
	case gorillaws.BinaryMessage:
		if ws.isPTY {
			// In PTY mode, all binary data is stdin
			n = copy(p, data)
			if n < len(data) {
				// Buffer remaining data
				ws.readBuf = data[n:]
			}
			return n, nil
		} else {
			// In non-PTY mode, check stream ID
			if len(data) == 0 {
				return 0, errors.New("empty message")
			}
			streamID := StreamID(data[0])
			if streamID == StreamStdin {
				payload := data[1:]
				n = copy(p, payload)
				if n < len(payload) {
					// Buffer remaining data
					ws.readBuf = payload[n:]
				}
				return n, nil
			} else if streamID == StreamStdinEOF {
				return 0, io.EOF
			}
			// Ignore other streams and try again
			return ws.Read(p)
		}
	case gorillaws.TextMessage:
		// Control messages are handled separately for PTY mode
		if ws.isPTY {
			return ws.Read(p) // Try again
		}
		// For non-PTY mode, text messages are not expected for data
		return ws.Read(p)
	default:
		return 0, errors.New("unsupported message type")
	}
}

// Write implements io.Writer for the WebSocket streams
func (ws *webSocketStreams) Write(p []byte) (n int, err error) {
	if ws.isPTY {
		// In PTY mode, write raw data
		err = ws.writeRaw(p)
	} else {
		// In non-PTY mode, write with stdout stream ID
		err = ws.writeStream(StreamStdout, p)
	}
	if err != nil {
		return 0, err
	}
	return len(p), nil
}

// writeRaw writes raw bytes to the WebSocket
func (ws *webSocketStreams) writeRaw(data []byte) error {
	result := make(chan error, 1)
	select {
	case ws.writeChan <- writeRequest{
		messageType: gorillaws.BinaryMessage,
		data:        data,
		result:      result,
	}:
		return <-result
	case <-ws.done:
		return errors.New("adapter closed")
	}
}

// writeStream writes data with a stream ID prefix
func (ws *webSocketStreams) writeStream(stream StreamID, data []byte) error {
	if ws.isPTY {
		// In PTY mode, just write raw data
		return ws.writeRaw(data)
	}

	// Prepend stream ID to data
	msg := make([]byte, len(data)+1)
	msg[0] = byte(stream)
	copy(msg[1:], data)

	return ws.writeRaw(msg)
}

// WriteExit writes an exit code message
func (ws *webSocketStreams) WriteExit(code int) error {
	if code < 0 || code > 255 {
		code = 255 // Cap at 255 for byte representation
	}
	return ws.writeStream(StreamExit, []byte{byte(code)})
}

// Close closes the WebSocket streams
func (ws *webSocketStreams) Close() error {
	close(ws.done)
	return nil
}
