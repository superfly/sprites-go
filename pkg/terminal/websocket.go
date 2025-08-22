//go:build !clientonly
// +build !clientonly

package terminal

import (
	"context"
	"encoding/json"
	"errors"
	"io"
	"net/http"
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
	wsStreams := newWebSocketStreams(conn, h.session.tty, h.session)
	defer wsStreams.Close()

	// Create a cancellable context that will be cancelled if websocket disconnects
	ctx, cancel := context.WithCancel(r.Context())
	defer cancel()

	// Monitor for websocket disconnection
	go func() {
		select {
		case <-wsStreams.readErrChan:
			// Websocket disconnected - kill container process first if tracked
			h.session.killContainerProcess()
			// Then cancel the context to kill the wrapper process
			cancel()
		case <-ctx.Done():
			// Context cancelled for other reasons
		}
	}()

	// Send ready signal to indicate session is starting
	// In TTY mode, we don't send stream-prefixed messages
	if !h.session.tty {
		readyData := []byte{byte(StreamReady)}
		wsStreams.writeChan <- writeRequest{
			messageType: gorillaws.BinaryMessage,
			data:        readyData,
		}
	}

	// Call onConnected callback if set
	if h.onConnected != nil {
		h.onConnected(wsStreams)
	}

	// Run the session - pass separate wrappers for stdout and stderr
	exitCode, err := h.session.Run(ctx, wsStreams, &streamWrapper{ws: wsStreams, streamID: StreamStdout}, &streamWrapper{ws: wsStreams, streamID: StreamStderr})
	if err != nil && h.session.logger != nil {
		h.session.logger.Error("Session run failed", "error", err)
	}

	// Send the exit code through the channel to ensure ordering
	// In TTY mode, we don't send exit codes as the client expects raw PTY data
	if !h.session.tty {
		exitData := make([]byte, 2)
		exitData[0] = byte(StreamExit)
		if exitCode < 0 || exitCode > 255 {
			exitCode = 255
		}
		exitData[1] = byte(exitCode)

		// Send exit code (guaranteed to be after all stdout/stderr)
		// Use synchronous write to ensure it's processed before handler returns
		done := make(chan error, 1)
		wsStreams.writeChan <- writeRequest{
			messageType: gorillaws.BinaryMessage,
			data:        exitData,
			done:        done,
		}
		<-done // Wait for exit code to be sent
	}

	// Send close message after exit code
	wsStreams.WriteClose()

	// Don't close the WebSocket - let the client close it
	// Start a timeout goroutine to close the connection if client doesn't close it
	go func() {
		select {
		case <-time.After(30 * time.Second): // 30 second timeout
			if h.session.logger != nil {
				h.session.logger.Debug("Closing WebSocket connection after timeout")
			}
			conn.Close()
		case <-ctx.Done():
			// Context was cancelled, connection will be closed by defer
		}
	}()

	return nil
}

// StreamID and ControlMessage types are now defined in stream_types.go

// webSocketStreams implements io.Reader, io.Writer for WebSocket communication
type webSocketStreams struct {
	conn    *gorillaws.Conn
	tty     bool
	readBuf []byte
	session *Session // Reference to session for resize calls

	// Channel for write requests
	writeChan chan writeRequest

	// Signal to stop the write loop
	closeChan chan struct{}

	// Signal when write loop has finished
	doneChan chan struct{}

	// Signal when a read error occurs (websocket disconnection)
	readErrChan chan error
}

type writeRequest struct {
	messageType int
	data        []byte
	done        chan error // nil for fire-and-forget
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
		err := w.ws.writeRaw(w.streamID, p)
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

// newWebSocketStreams creates new websocket streams for binary mode
func newWebSocketStreams(conn *gorillaws.Conn, tty bool, session *Session) *webSocketStreams {
	ws := &webSocketStreams{
		conn:        conn,
		tty:         tty,
		session:     session,
		writeChan:   make(chan writeRequest, 100), // Buffered for better performance
		closeChan:   make(chan struct{}),
		doneChan:    make(chan struct{}),
		readErrChan: make(chan error, 1), // Buffered to avoid blocking
	}

	// Start the write loop
	go ws.writeLoop()

	return ws
}

// writeLoop handles all writes sequentially, ensuring ordering (buffered channel doesn't affect ordering since only one goroutine reads from it)
func (ws *webSocketStreams) writeLoop() {
	defer close(ws.doneChan)

	for {
		select {
		case req := <-ws.writeChan:
			err := ws.conn.WriteMessage(req.messageType, req.data)
			if req.done != nil {
				req.done <- err
			}

		case <-ws.closeChan:
			// Process any remaining writes in the channel
			for {
				select {
				case req := <-ws.writeChan:
					err := ws.conn.WriteMessage(req.messageType, req.data)
					if req.done != nil {
						req.done <- err
					}
				default:
					return
				}
			}
		}
	}
}

// Read implements io.Reader for the WebSocket streams
func (ws *webSocketStreams) Read(p []byte) (n int, err error) {
	// Return buffered data first
	if len(ws.readBuf) > 0 {
		n = copy(p, ws.readBuf)
		ws.readBuf = ws.readBuf[n:]
		return n, nil
	}

	// Read new message from WebSocket
	messageType, data, err := ws.conn.ReadMessage()
	if err != nil {
		// Signal read error (websocket disconnection) to the handler
		select {
		case ws.readErrChan <- err:
		default:
			// Channel already has an error, don't block
		}
		return 0, err
	}

	// Handle different message types
	switch messageType {
	case gorillaws.BinaryMessage:
		if ws.tty {
			// PTY mode: all binary data is stdin
			n = copy(p, data)
			if n < len(data) {
				// Buffer remaining data
				ws.readBuf = data[n:]
			}
			return n, nil
		} else {
			// Non-PTY mode: check stream ID
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
		// Handle control messages
		if ws.tty {
			// Parse control message
			var controlMsg ControlMessage
			if err := json.Unmarshal(data, &controlMsg); err == nil {
				switch controlMsg.Type {
				case "resize":
					// Handle resize in PTY mode
					if ws.session.logger != nil {
						ws.session.logger.Debug("Received terminal resize via WebSocket",
							"cols", controlMsg.Cols, "rows", controlMsg.Rows)
					}
					ws.session.Resize(controlMsg.Cols, controlMsg.Rows)
					// Continue reading after handling resize
					return ws.Read(p)
				}
			}
		}
		// For non-PTY mode or unhandled text messages, try again
		return ws.Read(p)
	default:
		return 0, errors.New("unsupported message type")
	}
}

// Write implements io.Writer for the WebSocket streams
func (ws *webSocketStreams) Write(p []byte) (n int, err error) {
	if ws.tty {
		// PTY mode: write raw data
		err = ws.writeRaw(StreamStdout, p)
	} else {
		// Non-PTY mode: write with stdout stream ID
		err = ws.writeStream(StreamStdout, p)
	}
	if err != nil {
		return 0, err
	}
	return len(p), nil
}

// writeRaw writes raw data to the websocket
func (s *webSocketStreams) writeRaw(streamID StreamID, data []byte) error {
	var msgData []byte
	if s.tty {
		// PTY mode: no stream ID
		msgData = data
	} else {
		// Non-PTY mode: add stream ID prefix
		msgData = make([]byte, len(data)+1)
		msgData[0] = byte(streamID)
		copy(msgData[1:], data)
	}

	// For PTY mode, use synchronous write to ensure ordering
	if s.tty {
		done := make(chan error, 1)
		req := writeRequest{
			messageType: gorillaws.BinaryMessage,
			data:        msgData,
			done:        done,
		}
		s.writeChan <- req
		return <-done
	}

	req := writeRequest{
		messageType: gorillaws.BinaryMessage,
		data:        msgData,
		done:        make(chan error, 1),
	}

	s.writeChan <- req
	return <-req.done
}

// writeStream writes data to the WebSocket with the specified stream ID
func (ws *webSocketStreams) writeStream(stream StreamID, data []byte) error {
	req := writeRequest{
		messageType: gorillaws.BinaryMessage,
		data:        make([]byte, len(data)+1), // +1 for stream ID
		done:        make(chan error, 1),
	}
	req.data[0] = byte(stream)
	copy(req.data[1:], data)

	ws.writeChan <- req
	return <-req.done
}

// WriteExit writes an exit code message
func (ws *webSocketStreams) WriteExit(code int) error {
	if code < 0 || code > 255 {
		code = 255 // Cap at 255 for byte representation
	}
	return ws.writeStream(StreamExit, []byte{byte(code)})
}

// WriteClose sends a close message
func (ws *webSocketStreams) WriteClose() error {
	req := writeRequest{
		messageType: gorillaws.CloseMessage,
		data:        gorillaws.FormatCloseMessage(gorillaws.CloseNormalClosure, ""),
	}
	ws.writeChan <- req
	return nil
}

// WriteTextMessage writes a raw text message as a text WebSocket frame
func (ws *webSocketStreams) WriteTextMessage(data []byte) error {
	req := writeRequest{
		messageType: gorillaws.TextMessage,
		data:        data,
	}
	ws.writeChan <- req
	return nil
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

// Close closes the WebSocket streams
func (ws *webSocketStreams) Close() error {
	// Non-blocking close - if already closed, this is a no-op
	select {
	case <-ws.closeChan:
		// Already closed
	default:
		close(ws.closeChan)
	}

	// Wait for writeLoop to finish, but with a timeout to prevent hanging
	select {
	case <-ws.doneChan:
		// Write loop exited cleanly
	case <-time.After(5 * time.Second):
		// Write loop didn't exit in time - probably blocked on a write
		// Continue anyway to prevent hanging the entire process
	}
	return nil
}
