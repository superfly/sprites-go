package wsexec

import (
	"encoding/json"
	"errors"
	"fmt"
	"sync"
	"time"

	gorillaws "github.com/gorilla/websocket"
)

// MessageType represents the type of WebSocket message
type MessageType uint8

const (
	MessageTypeStdin MessageType = iota
	MessageTypeStdout
	MessageTypeStderr
	MessageTypeStdinEOF
	MessageTypeExit
	MessageTypeError
	MessageTypeResize
	MessageTypePing
	MessageTypePong
)

// Message represents a WebSocket message
type Message struct {
	Type MessageType `json:"type"`
	Data []byte      `json:"data"`
}

// ResizeMessage represents a terminal resize message
type ResizeMessage struct {
	Width  uint16 `json:"width"`
	Height uint16 `json:"height"`
}

// ExitMessage represents a command exit message
type ExitMessage struct {
	Code int `json:"code"`
}

// ErrorMessage represents an error message
type ErrorMessage struct {
	Error string `json:"error"`
}

// Adapter wraps a gorilla WebSocket connection for our protocol
type Adapter struct {
	conn   *gorillaws.Conn
	mu     sync.Mutex
	closed bool
}

// NewAdapter creates a new WebSocket adapter
func NewAdapter(conn *gorillaws.Conn) *Adapter {
	return &Adapter{
		conn: conn,
	}
}

// WriteMessage writes a message to the WebSocket
func (a *Adapter) WriteMessage(msg *Message) error {
	data, err := json.Marshal(msg)
	if err != nil {
		return err
	}

	a.mu.Lock()
	defer a.mu.Unlock()

	if a.closed {
		return gorillaws.ErrCloseSent
	}

	return a.conn.WriteMessage(gorillaws.BinaryMessage, data)
}

// WriteStdin writes stdin data
func (a *Adapter) WriteStdin(data []byte) error {
	return a.WriteMessage(&Message{
		Type: MessageTypeStdin,
		Data: data,
	})
}

// WriteStdinEOF signals that stdin has been closed
func (a *Adapter) WriteStdinEOF() error {
	return a.WriteMessage(&Message{
		Type: MessageTypeStdinEOF,
		Data: []byte{},
	})
}

// WriteStdout writes stdout data
func (a *Adapter) WriteStdout(data []byte) error {
	return a.WriteMessage(&Message{
		Type: MessageTypeStdout,
		Data: data,
	})
}

// WriteStderr writes stderr data
func (a *Adapter) WriteStderr(data []byte) error {
	return a.WriteMessage(&Message{
		Type: MessageTypeStderr,
		Data: data,
	})
}

// WriteResize writes a resize message
func (a *Adapter) WriteResize(width, height uint16) error {
	resize := ResizeMessage{Width: width, Height: height}
	data, err := json.Marshal(resize)
	if err != nil {
		return err
	}
	return a.WriteMessage(&Message{
		Type: MessageTypeResize,
		Data: data,
	})
}

// WriteExit writes an exit message
func (a *Adapter) WriteExit(code int) error {
	exit := ExitMessage{Code: code}
	data, err := json.Marshal(exit)
	if err != nil {
		return err
	}
	return a.WriteMessage(&Message{
		Type: MessageTypeExit,
		Data: data,
	})
}

// WriteError writes an error message
func (a *Adapter) WriteError(err error) error {
	if err == nil {
		return nil
	}
	errMsg := ErrorMessage{Error: err.Error()}
	data, err := json.Marshal(errMsg)
	if err != nil {
		return err
	}
	return a.WriteMessage(&Message{
		Type: MessageTypeError,
		Data: data,
	})
}

// WritePing writes a ping message
func (a *Adapter) WritePing() error {
	return a.WriteMessage(&Message{
		Type: MessageTypePing,
		Data: nil,
	})
}

// WritePong writes a pong message
func (a *Adapter) WritePong() error {
	return a.WriteMessage(&Message{
		Type: MessageTypePong,
		Data: nil,
	})
}

// ReadMessage reads a message from the WebSocket
func (a *Adapter) ReadMessage() (*Message, error) {
	messageType, data, err := a.conn.ReadMessage()
	if err != nil {
		return nil, err
	}

	// We only handle binary messages
	if messageType != gorillaws.BinaryMessage {
		return nil, errors.New("invalid message type: only binary messages are supported")
	}

	var msg Message
	if err := json.Unmarshal(data, &msg); err != nil {
		return nil, err
	}

	return &msg, nil
}

// Close closes the WebSocket connection
func (a *Adapter) Close() error {
	a.mu.Lock()
	defer a.mu.Unlock()

	if a.closed {
		return nil
	}

	a.closed = true

	// Send close message with timeout
	deadline := time.Now().Add(5 * time.Second)
	a.conn.WriteControl(gorillaws.CloseMessage, gorillaws.FormatCloseMessage(gorillaws.CloseNormalClosure, ""), deadline)

	return a.conn.Close()
}

// Ping sends a ping message
func (a *Adapter) Ping() error {
	a.mu.Lock()
	defer a.mu.Unlock()

	if a.closed {
		return gorillaws.ErrCloseSent
	}

	deadline := time.Now().Add(5 * time.Second)
	return a.conn.WriteControl(gorillaws.PingMessage, []byte{}, deadline)
}

// DecodeResize decodes resize message data
func DecodeResize(data []byte) (width, height uint16, err error) {
	var resize ResizeMessage
	err = json.Unmarshal(data, &resize)
	return resize.Width, resize.Height, err
}

// DecodeExit decodes exit message data
func DecodeExit(data []byte) (code int, err error) {
	var exit ExitMessage
	err = json.Unmarshal(data, &exit)
	return exit.Code, err
}

// DecodeError decodes error message data
func DecodeError(data []byte) error {
	var errMsg ErrorMessage
	if err := json.Unmarshal(data, &errMsg); err != nil {
		return err
	}
	return fmt.Errorf("%s", errMsg.Error)
}
