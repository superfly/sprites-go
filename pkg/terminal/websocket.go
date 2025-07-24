package terminal

import (
	"encoding/json"
	"errors"
	"io"
	"net/http"
	"sync"
	"time"

	gorillaws "github.com/gorilla/websocket"
)

// TextMessageSender allows sending text messages through the websocket
type TextMessageSender interface {
	SendTextMessage(data []byte) error
}

// WebSocketHandler wraps a terminal Session to provide WebSocket connectivity.
type WebSocketHandler struct {
	session     *Session
	upgrader    gorillaws.Upgrader
	onConnected func(sender TextMessageSender) // called when websocket is connected
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

// WithOnConnected sets a callback that is called when the websocket connection is established
func (h *WebSocketHandler) WithOnConnected(callback func(sender TextMessageSender)) *WebSocketHandler {
	h.onConnected = callback
	return h
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

	// Call onConnected callback if set
	if h.onConnected != nil {
		h.onConnected(wsStreams)
	}

	// Run the session - pass separate wrappers for stdout and stderr
	ctx := r.Context()
	exitCode, err := h.session.Run(ctx, wsStreams, &streamWrapper{ws: wsStreams, streamID: StreamStdout}, &streamWrapper{ws: wsStreams, streamID: StreamStderr})

	// Flush all pending writes with a longer timeout
	// This ensures all buffered output is sent before closing
	flushStart := time.Now()
	flushTimeout := 2 * time.Second
	if flushErr := wsStreams.Flush(flushTimeout); flushErr != nil {
		flushDuration := time.Since(flushStart)
		if flushErr.Error() == "flush timeout" || flushErr.Error() == "flush timeout - write channel full" {
			// This is a serious issue - data may be lost
			if h.session.logger != nil {
				h.session.logger.Error("WebSocket flush timed out - data may be lost",
					"timeout", flushTimeout,
					"duration", flushDuration,
					"error", flushErr)
			}
		} else {
			// Other flush errors (like adapter closed)
			if h.session.logger != nil {
				h.session.logger.Warn("WebSocket flush error",
					"duration", flushDuration,
					"error", flushErr)
			}
		}
	} else {
		// Flush succeeded
		flushDuration := time.Since(flushStart)
		if h.session.logger != nil && flushDuration > 100*time.Millisecond {
			// Log if flush took longer than expected
			h.session.logger.Debug("WebSocket flush completed",
				"duration", flushDuration)
		}
	}

	// Send exit code
	if err := wsStreams.WriteExit(exitCode); err != nil {
		// Log error but don't fail
	}

	// Send close message through the write channel to ensure proper ordering
	// This guarantees the close frame is sent after all data frames
	if err := wsStreams.WriteClose(); err != nil {
		if h.session.logger != nil {
			h.session.logger.Warn("Failed to send WebSocket close message",
				"error", err)
		}
	}

	// Wait for client close
	deadline := time.Now().Add(2 * time.Second)
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
	conn        *gorillaws.Conn
	readBuf     []byte
	readMu      sync.Mutex
	writeChan   chan writeRequest
	done        chan struct{}
	tty         bool
	writeErrorMu sync.RWMutex
	lastWriteErr error
}

type writeRequest struct {
	messageType int
	data        []byte
	result      chan error
}

// streamWrapper wraps webSocketStreams to write to a specific stream
type streamWrapper struct {
	ws       *webSocketStreams
	streamID StreamID
}

// Write implements io.Writer for a specific stream
func (w *streamWrapper) Write(p []byte) (int, error) {
	if w.ws.tty {
		// In PTY mode, write raw data
		err := w.ws.writeRaw(p)
		if err != nil {
			return 0, err
		}
		return len(p), nil
	}
	// In non-PTY mode, write with the specific stream ID
	err := w.ws.writeStream(w.streamID, p)
	if err != nil {
		return 0, err
	}
	return len(p), nil
}

// newWebSocketStreams creates a new WebSocket stream handler
func newWebSocketStreams(conn *gorillaws.Conn, tty bool) *webSocketStreams {
	ws := &webSocketStreams{
		conn:      conn,
		tty:       tty,
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
			// Handle flush request
			if req.messageType == -1 {
				// This is a flush request - marker that all previous writes are done
				if req.result != nil {
					ws.writeErrorMu.RLock()
					err := ws.lastWriteErr
					ws.writeErrorMu.RUnlock()
					req.result <- err
				}
				continue
			}

			// Normal write request
			if req.messageType == gorillaws.CloseMessage {
				// Use WriteControl for close messages
				deadline := time.Now().Add(2 * time.Second)
				err := ws.conn.WriteControl(req.messageType, req.data, deadline)
				if err != nil {
					ws.writeErrorMu.Lock()
					ws.lastWriteErr = err
					ws.writeErrorMu.Unlock()
				}
				if req.result != nil {
					req.result <- err
				}
			} else {
				// Use WriteMessage for regular messages
				err := ws.conn.WriteMessage(req.messageType, req.data)
				if err != nil {
					ws.writeErrorMu.Lock()
					ws.lastWriteErr = err
					ws.writeErrorMu.Unlock()
				}
				if req.result != nil {
					req.result <- err
				}
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
		if ws.tty {
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
		if ws.tty {
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
	if ws.tty {
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
	if ws.tty {
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

// WriteClose sends a close message through the write channel to ensure proper ordering
func (ws *webSocketStreams) WriteClose() error {
	closeData := gorillaws.FormatCloseMessage(gorillaws.CloseNormalClosure, "")
	
	// Create a result channel to wait for the write to complete
	result := make(chan error, 1)
	
	select {
	case ws.writeChan <- writeRequest{
		messageType: gorillaws.CloseMessage,
		data:        closeData,
		result:      result,
	}:
		// Wait for the write to complete
		return <-result
	case <-ws.done:
		return errors.New("adapter closed")
	}
}

// WriteTextMessage writes a raw text message as a text WebSocket frame
func (ws *webSocketStreams) WriteTextMessage(data []byte) error {
	result := make(chan error, 1)
	select {
	case ws.writeChan <- writeRequest{
		messageType: gorillaws.TextMessage,
		data:        data,
		result:      result,
	}:
		return <-result
	case <-ws.done:
		return errors.New("adapter closed")
	}
}

// SendTextMessage implements the TextMessageSender interface
func (ws *webSocketStreams) SendTextMessage(data []byte) error {
	return ws.WriteTextMessage(data)
}

// WriteControlMessage writes a control message as a text WebSocket frame
func (ws *webSocketStreams) WriteControlMessage(msg ControlMessage) error {
	data, err := json.Marshal(msg)
	if err != nil {
		return err
	}
	return ws.WriteTextMessage(data)
}

// Flush waits for all pending writes to complete
func (ws *webSocketStreams) Flush(timeout time.Duration) error {
	// Create a flush request with a result channel
	result := make(chan error, 1)
	timer := time.NewTimer(timeout)
	defer timer.Stop()

	select {
	case ws.writeChan <- writeRequest{
		messageType: -1, // Special marker for flush
		result:      result,
	}:
		// Wait for the flush to complete or timeout
		select {
		case err := <-result:
			return err
		case <-timer.C:
			return errors.New("flush timeout")
		case <-ws.done:
			return errors.New("adapter closed")
		}
	case <-timer.C:
		return errors.New("flush timeout - write channel full")
	case <-ws.done:
		return errors.New("adapter closed")
	}
}

// Close closes the WebSocket streams
func (ws *webSocketStreams) Close() error {
	close(ws.done)
	return nil
}
