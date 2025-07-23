package terminal

import (
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"

	gorillaws "github.com/gorilla/websocket"
)

// TestWebSocketStderrFix specifically tests that stderr is sent with the correct stream ID
// This test verifies the fix for the bug where all output was being sent as stdout
func TestWebSocketStderrFix(t *testing.T) {
	// Create a session that outputs to both stdout and stderr
	session := NewSession(
		WithCommand("sh", "-c", "echo 'This is stdout'; echo 'This is stderr' >&2"),
		WithTTY(false),
	)

	handler := NewWebSocketHandler(session)
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if err := handler.Handle(w, r); err != nil {
			t.Errorf("handler error: %v", err)
		}
	}))
	defer server.Close()

	// Connect as client
	wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
	dialer := gorillaws.DefaultDialer
	conn, _, err := dialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("failed to connect: %v", err)
	}
	defer conn.Close()

	// Track what we receive
	type message struct {
		streamID StreamID
		content  string
	}
	var messages []message
	done := make(chan struct{})

	go func() {
		defer close(done)
		for {
			messageType, data, err := conn.ReadMessage()
			if err != nil {
				return
			}

			if messageType == gorillaws.BinaryMessage && len(data) > 0 {
				stream := StreamID(data[0])
				payload := data[1:]

				switch stream {
				case StreamStdout, StreamStderr:
					messages = append(messages, message{
						streamID: stream,
						content:  string(payload),
					})
				case StreamExit:
					return
				}
			}
		}
	}()

	<-done

	// Verify we received both stdout and stderr with correct stream IDs
	var gotStdout, gotStderr bool
	for _, msg := range messages {
		switch msg.streamID {
		case StreamStdout:
			if strings.Contains(msg.content, "This is stdout") {
				gotStdout = true
			}
			if strings.Contains(msg.content, "This is stderr") {
				t.Errorf("stderr content found in stdout stream: %q", msg.content)
			}
		case StreamStderr:
			if strings.Contains(msg.content, "This is stderr") {
				gotStderr = true
			}
			if strings.Contains(msg.content, "This is stdout") {
				t.Errorf("stdout content found in stderr stream: %q", msg.content)
			}
		}
	}

	if !gotStdout {
		t.Error("stdout content not received on stdout stream")
	}
	if !gotStderr {
		t.Error("stderr content not received on stderr stream")
	}

	// Log what we received for debugging
	t.Logf("Received %d messages:", len(messages))
	for i, msg := range messages {
		streamName := "unknown"
		switch msg.streamID {
		case StreamStdout:
			streamName = "stdout"
		case StreamStderr:
			streamName = "stderr"
		}
		t.Logf("  Message %d: stream=%s (0x%02x), content=%q", i+1, streamName, msg.streamID, msg.content)
	}
}
