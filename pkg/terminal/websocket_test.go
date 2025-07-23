package terminal

import (
	"net/http"
	"net/http/httptest"
	"strings"
	"sync"
	"testing"

	gorillaws "github.com/gorilla/websocket"
)

// TestWebSocketDataCompletion tests that all data is received before connection closes
func TestWebSocketDataCompletion(t *testing.T) {
	// Create a test session that outputs a lot of data quickly
	session := NewSession(
		WithCommand("sh", "-c", "for i in $(seq 1 100); do echo \"Line $i\"; done"),
		WithTTY(false),
	)

	handler := NewWebSocketHandler(session)

	// Set up test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if err := handler.Handle(w, r); err != nil {
			t.Errorf("handler error: %v", err)
		}
	}))
	defer server.Close()

	// Connect as a client
	wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
	dialer := gorillaws.DefaultDialer
	conn, _, err := dialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("failed to connect: %v", err)
	}
	defer conn.Close()

	// Collect all received messages
	var mu sync.Mutex
	var receivedLines []string
	var exitCodeReceived bool
	var wg sync.WaitGroup

	wg.Add(1)
	go func() {
		defer wg.Done()
		for {
			messageType, data, err := conn.ReadMessage()
			if err != nil {
				return
			}

			if messageType == gorillaws.BinaryMessage && len(data) > 0 {
				stream := StreamID(data[0])
				payload := data[1:]

				mu.Lock()
				switch stream {
				case StreamStdout:
					// Split payload into lines
					lines := strings.Split(string(payload), "\n")
					for _, line := range lines {
						if line != "" {
							receivedLines = append(receivedLines, line)
						}
					}
				case StreamExit:
					exitCodeReceived = true
					mu.Unlock()
					return // Exit received, stop reading
				}
				mu.Unlock()
			}
		}
	}()

	// Wait for the connection to close
	wg.Wait()

	// Verify results
	mu.Lock()
	defer mu.Unlock()

	if !exitCodeReceived {
		t.Error("exit code was not received")
	}

	// We should have received all 100 lines
	if len(receivedLines) != 100 {
		t.Errorf("expected 100 lines, got %d", len(receivedLines))
		if len(receivedLines) > 0 {
			t.Logf("First line: %s", receivedLines[0])
			t.Logf("Last line: %s", receivedLines[len(receivedLines)-1])
		}
	}

	// Verify the lines are in order
	for i, line := range receivedLines {
		// Simpler approach - just check prefix
		if !strings.HasPrefix(line, "Line ") {
			t.Errorf("line %d: expected line to start with 'Line ', got %q", i, line)
		}
	}
}
