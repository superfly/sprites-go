package terminal

// StreamID represents the stream identifier for non-PTY mode
type StreamID byte

const (
	StreamStdin    StreamID = 0x00
	StreamStdout   StreamID = 0x01
	StreamStderr   StreamID = 0x02
	StreamExit     StreamID = 0x03
	StreamStdinEOF StreamID = 0x04 // Explicit EOF signal
	StreamReady    StreamID = 0x05 // Indicates session is ready
	StreamResize   StreamID = 0x06 // Terminal resize events (used in wsclient)
	StreamText     StreamID = 0x07 // Text messages (used in wsclient)
)

// ControlMessage represents a control message sent via text WebSocket frames
type ControlMessage struct {
	Type string `json:"type"`
	// Resize fields
	Cols uint16 `json:"cols,omitempty"`
	Rows uint16 `json:"rows,omitempty"`
	// Additional fields that might be used
	Width  uint16 `json:"width,omitempty"`
	Height uint16 `json:"height,omitempty"`
}
