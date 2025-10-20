package wss

import (
	"io"
)

// OpConn is the gorilla-compatible subset exposed to operation handlers.
// It intentionally mirrors a minimal subset to allow reuse of existing code
// that expects a gorilla websocket connection.
type OpConn interface {
	ReadMessage() (int, []byte, error)
	NextReader() (int, io.Reader, error)
	WriteMessage(int, []byte) error
	WriteJSON(v any) error
	Close() error
}
