package terminal

import (
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
	"time"

	gorillaws "github.com/gorilla/websocket"
	"github.com/stretchr/testify/require"
)

// TestRawWebSocketCloseFlow tests the raw WebSocket close behavior
func TestRawWebSocketCloseFlow(t *testing.T) {
	// Create a simple echo server that closes after sending a message
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		upgrader := gorillaws.Upgrader{}
		conn, err := upgrader.Upgrade(w, r, nil)
		require.NoError(t, err)
		defer conn.Close()

		// Send a message
		err = conn.WriteMessage(gorillaws.TextMessage, []byte("hello"))
		require.NoError(t, err)

		// Send close message
		closeData := gorillaws.FormatCloseMessage(gorillaws.CloseNormalClosure, "server closing")
		err = conn.WriteControl(gorillaws.CloseMessage, closeData, time.Now().Add(time.Second))
		require.NoError(t, err)

		// Wait a bit for client to respond with close
		conn.SetReadDeadline(time.Now().Add(2 * time.Second))
		for {
			_, _, err := conn.ReadMessage()
			if err != nil {
				break
			}
		}
	}))
	defer server.Close()

	// Connect as client
	wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
	dialer := gorillaws.Dialer{}
	conn, _, err := dialer.Dial(wsURL, nil)
	require.NoError(t, err)
	defer conn.Close()

	// Read messages
	msgCount := 0
	closeReceived := false

	for i := 0; i < 5; i++ { // Try reading a few times
		messageType, data, err := conn.ReadMessage()
		if err != nil {
			if closeErr, ok := err.(*gorillaws.CloseError); ok {
				t.Logf("Got close error: code=%d, text=%s", closeErr.Code, closeErr.Text)
				closeReceived = true
				break
			}
			t.Logf("Read error: %v", err)
			break
		}

		msgCount++
		t.Logf("Got message type=%d, data=%s", messageType, string(data))

		if messageType == gorillaws.CloseMessage {
			t.Log("Got close message")
			closeReceived = true
			break
		}
	}

	if !closeReceived {
		t.Fatal("Did not receive close notification from server")
	}
}
