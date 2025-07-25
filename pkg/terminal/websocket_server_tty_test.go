package terminal

import (
	"bytes"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
	"time"

	gorillaws "github.com/gorilla/websocket"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestWebSocketServerTTYExit verifies that the server properly closes the WebSocket
// connection when a TTY process exits
func TestWebSocketServerTTYExit(t *testing.T) {
	// Create a session that exits immediately
	session := NewSession(
		WithCommand("sh", "-c", "echo 'process started'; echo 'process exiting'"),
		WithTTY(true),
	)

	handler := NewWebSocketHandler(session)
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		t.Log("Server: Handling WebSocket request")
		if err := handler.Handle(w, r); err != nil {
			t.Errorf("handler error: %v", err)
		}
		t.Log("Server: Handler returned")
	}))
	defer server.Close()

	// Connect to the WebSocket server
	wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
	dialer := gorillaws.Dialer{}
	conn, _, err := dialer.Dial(wsURL, nil)
	require.NoError(t, err)
	defer conn.Close()

	// Collect all output
	var output bytes.Buffer
	closeReceived := false

	// Set a timeout for reading
	timeout := time.After(5 * time.Second)
	done := make(chan bool)

	go func() {
		// Read messages until we get a close error
		for {
			messageType, data, err := conn.ReadMessage()
			if err != nil {
				// Check if it's a close error - this is how gorilla websocket signals close
				if closeErr, ok := err.(*gorillaws.CloseError); ok {
					t.Logf("Got close error: code=%d, text=%s", closeErr.Code, closeErr.Text)
					closeReceived = closeErr.Code == gorillaws.CloseNormalClosure
				} else {
					t.Logf("Got error: %v", err)
				}
				done <- true
				return
			}

			t.Logf("Got message: type=%d, len=%d", messageType, len(data))
			if messageType == gorillaws.BinaryMessage {
				output.Write(data)
			}
		}
	}()

	// Wait for either completion or timeout
	select {
	case <-done:
		t.Log("Read loop completed")
	case <-timeout:
		t.Fatal("Test timed out - server did not close connection")
	}

	// Verify we received the close
	assert.True(t, closeReceived, "Should have received close notification")

	// Verify we got output
	outputStr := output.String()
	t.Logf("Output: %q", outputStr)
	assert.Contains(t, outputStr, "process started")
	assert.Contains(t, outputStr, "process exiting")
}

// TestWebSocketServerTTYCloseMessage verifies that the server sends a proper close message
func TestWebSocketServerTTYCloseMessage(t *testing.T) {
	// Create a session that exits after a short delay
	session := NewSession(
		WithCommand("sh", "-c", "echo 'hello'; sleep 0.1; echo 'goodbye'"),
		WithTTY(true),
	)

	handler := NewWebSocketHandler(session)
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if err := handler.Handle(w, r); err != nil {
			t.Errorf("handler error: %v", err)
		}
	}))
	defer server.Close()

	// Connect to the WebSocket server
	wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
	dialer := gorillaws.Dialer{}
	conn, _, err := dialer.Dial(wsURL, nil)
	require.NoError(t, err)
	defer conn.Close()

	// Set up close handler to capture close message
	closeReceived := make(chan struct{})
	conn.SetCloseHandler(func(code int, text string) error {
		assert.Equal(t, gorillaws.CloseNormalClosure, code, "Expected normal closure code")
		close(closeReceived)
		return nil
	})

	// Read messages in a goroutine
	go func() {
		for {
			_, _, err := conn.ReadMessage()
			if err != nil {
				return
			}
		}
	}()

	// Wait for the close handler to be called
	select {
	case <-closeReceived:
		// Good - close message was received
	case <-time.After(3 * time.Second):
		t.Fatal("Server did not send close message after process exited")
	}
}

// TestWebSocketServerTTYWithStdin verifies server handles TTY with stdin correctly
func TestWebSocketServerTTYWithStdin(t *testing.T) {
	// Create a session that reads input and echoes it back
	session := NewSession(
		WithCommand("sh", "-c", "read line; echo \"Got: $line\""),
		WithTTY(true),
	)

	handler := NewWebSocketHandler(session)
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if err := handler.Handle(w, r); err != nil {
			t.Errorf("handler error: %v", err)
		}
	}))
	defer server.Close()

	// Connect to the WebSocket server
	wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
	dialer := gorillaws.Dialer{}
	conn, _, err := dialer.Dial(wsURL, nil)
	require.NoError(t, err)
	defer conn.Close()

	// Send input
	inputMsg := []byte("test input\n")
	err = conn.WriteMessage(gorillaws.BinaryMessage, inputMsg)
	require.NoError(t, err)

	// Collect output
	var output bytes.Buffer
	readDone := make(chan error, 1)

	go func() {
		for {
			messageType, data, err := conn.ReadMessage()
			if err != nil {
				readDone <- err
				return
			}
			if messageType == gorillaws.BinaryMessage {
				output.Write(data)
				// Check if we got the expected output
				if strings.Contains(output.String(), "Got: test input") {
					readDone <- nil
					return
				}
			}
		}
	}()

	// Wait for expected output or timeout
	select {
	case err := <-readDone:
		if err != nil && !isNormalClose(err) {
			t.Errorf("Read error: %v", err)
		}
	case <-time.After(2 * time.Second):
		t.Fatal("Timeout waiting for output")
	}

	// Verify output
	assert.Contains(t, output.String(), "Got: test input")
}

func isNormalClose(err error) bool {
	if closeErr, ok := err.(*gorillaws.CloseError); ok {
		return closeErr.Code == gorillaws.CloseNormalClosure
	}
	return false
}
