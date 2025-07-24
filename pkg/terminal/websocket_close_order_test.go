package terminal

import (
	"testing"
	"time"

	gorillaws "github.com/gorilla/websocket"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestWebSocketCloseFrameOrdering verifies that the close frame is sent
// after all data frames, even for fast-exiting commands
func TestWebSocketCloseFrameOrdering(t *testing.T) {
	tests := []struct {
		name    string
		command []string
	}{
		{
			name:    "echo_single_char",
			command: []string{"echo", "1"},
		},
		{
			name:    "echo_hello",
			command: []string{"echo", "hello world"},
		},
		{
			name:    "printf_no_newline",
			command: []string{"printf", "test"},
		},
		{
			name:    "pwd",
			command: []string{"pwd"},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Create mock connection that tracks message order
			mockConn := &messageOrderTracker{
				messages: make([]trackedMessage, 0),
			}

			// Create websocket streams
			ws := &webSocketStreams{
				conn:      mockConn,
				writeChan: make(chan writeRequest, 100),
				done:      make(chan struct{}),
				tty:       false,
			}

			// Start write loop
			go ws.writeLoop()

			// Simulate command output
			err := ws.writeStream(StreamStdout, []byte("test output\n"))
			require.NoError(t, err)

			// Simulate exit code
			err = ws.WriteExit(0)
			require.NoError(t, err)

			// Send close frame through write channel
			err = ws.WriteClose()
			require.NoError(t, err)

			// Give time for messages to be processed
			time.Sleep(50 * time.Millisecond)

			// Verify message order
			require.Len(t, mockConn.messages, 3, "Should have 3 messages")

			// First should be stdout
			assert.Equal(t, gorillaws.BinaryMessage, mockConn.messages[0].messageType)
			assert.Equal(t, StreamStdout, StreamID(mockConn.messages[0].data[0]))

			// Second should be exit
			assert.Equal(t, gorillaws.BinaryMessage, mockConn.messages[1].messageType)
			assert.Equal(t, StreamExit, StreamID(mockConn.messages[1].data[0]))

			// Third should be close
			assert.Equal(t, gorillaws.CloseMessage, mockConn.messages[2].messageType)
			assert.Equal(t, "close frame", mockConn.messages[2].source)

			// Clean up
			ws.Close()
		})
	}
}

// messageOrderTracker tracks the order of messages
type trackedMessage struct {
	messageType int
	data        []byte
	source      string // "write" or "close frame"
}

type messageOrderTracker struct {
	messages []trackedMessage
}

func (m *messageOrderTracker) WriteMessage(messageType int, data []byte) error {
	m.messages = append(m.messages, trackedMessage{
		messageType: messageType,
		data:        data,
		source:      "write",
	})
	return nil
}

func (m *messageOrderTracker) WriteControl(messageType int, data []byte, deadline time.Time) error {
	m.messages = append(m.messages, trackedMessage{
		messageType: messageType,
		data:        data,
		source:      "close frame",
	})
	return nil
}

func (m *messageOrderTracker) ReadMessage() (messageType int, p []byte, err error) {
	return 0, nil, nil
}

func (m *messageOrderTracker) Close() error {
	return nil
}

func (m *messageOrderTracker) SetReadDeadline(t time.Time) error {
	return nil
}
