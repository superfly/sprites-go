package terminal

import (
	"net/http"
	"net/http/httptest"
	"strings"
	"sync"
	"testing"
	"time"

	gorillaws "github.com/gorilla/websocket"
)

// TestWebSocketLargeDataBeforeClose verifies that clients can receive large data
// before the WebSocket connection is closed
func TestWebSocketLargeDataBeforeClose(t *testing.T) {
	testCases := []struct {
		name         string
		command      []string
		minStdout    int
		minStderr    int
		description  string
	}{
		{
			name:         "10MB_stdout_websocket",
			command:      []string{"sh", "-c", "dd if=/dev/zero bs=1048576 count=10 2>/dev/null | base64"},
			minStdout:    10 * 1024 * 1024,
			minStderr:    0,
			description:  "10MB stdout through WebSocket",
		},
		{
			name:         "5MB_stderr_websocket",
			command:      []string{"sh", "-c", "dd if=/dev/zero bs=1048576 count=5 | base64 >&2"},
			minStdout:    0,
			minStderr:    5 * 1024 * 1024,
			description:  "5MB stderr through WebSocket",
		},
		{
			name:         "rapid_lines_websocket",
			command:      []string{"sh", "-c", "for i in $(seq 1 5000); do echo \"Line $i\"; done"},
			minStdout:    20000, // Rough estimate
			minStderr:    0,
			description:  "5000 lines through WebSocket",
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			// Run multiple iterations to catch race conditions
			for iter := 0; iter < 3; iter++ {
				t.Logf("Iteration %d: %s", iter, tc.description)
				
				session := NewSession(
					WithCommand(tc.command[0], tc.command[1:]...),
					WithTTY(false),
				)

				handler := NewWebSocketHandler(session)
				server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
					if err := handler.Handle(w, r); err != nil {
						t.Errorf("handler error: %v", err)
					}
				}))
				defer server.Close()

				// Connect as WebSocket client
				wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
				dialer := gorillaws.DefaultDialer
				conn, _, err := dialer.Dial(wsURL, nil)
				if err != nil {
					t.Fatalf("failed to connect: %v", err)
				}
				defer conn.Close()

				// Collect all data
				var mu sync.Mutex
				stdoutData := []byte{}
				stderrData := []byte{}
				exitReceived := false
				closeReceived := false

				done := make(chan struct{})
				go func() {
					defer close(done)
					for {
						messageType, data, err := conn.ReadMessage()
						if err != nil {
							// Check if it's a close error
							if gorillaws.IsCloseError(err, gorillaws.CloseNormalClosure) {
								mu.Lock()
								closeReceived = true
								mu.Unlock()
							}
							return
						}

						if messageType == gorillaws.BinaryMessage && len(data) > 0 {
							stream := StreamID(data[0])
							payload := data[1:]

							mu.Lock()
							switch stream {
							case StreamStdout:
								stdoutData = append(stdoutData, payload...)
							case StreamStderr:
								stderrData = append(stderrData, payload...)
							case StreamExit:
								exitReceived = true
							}
							mu.Unlock()
						}
					}
				}()

				// Wait for completion
				select {
				case <-done:
				case <-time.After(30 * time.Second):
					t.Fatal("timeout waiting for WebSocket data")
				}

				// Verify results
				mu.Lock()
				defer mu.Unlock()

				if !exitReceived {
					t.Error("exit code was not received")
				}

				if !closeReceived {
					t.Error("WebSocket close was not received")
				}

				if len(stdoutData) < tc.minStdout {
					t.Errorf("stdout too small: expected at least %d bytes, got %d", 
						tc.minStdout, len(stdoutData))
				}

				if len(stderrData) < tc.minStderr {
					t.Errorf("stderr too small: expected at least %d bytes, got %d", 
						tc.minStderr, len(stderrData))
				}

				t.Logf("Received stdout=%d bytes, stderr=%d bytes", 
					len(stdoutData), len(stderrData))
			}
		})
	}
}

// TestWebSocketCloseSequence verifies the proper order of operations during close
func TestWebSocketCloseSequence(t *testing.T) {
	session := NewSession(
		WithCommand("sh", "-c", "echo 'Final output'; exit 0"),
		WithTTY(false),
	)

	handler := NewWebSocketHandler(session)
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if err := handler.Handle(w, r); err != nil {
			t.Errorf("handler error: %v", err)
		}
	}))
	defer server.Close()

	wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
	dialer := gorillaws.DefaultDialer
	conn, _, err := dialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("failed to connect: %v", err)
	}
	defer conn.Close()

	// Track the sequence of events
	events := []string{}
	var mu sync.Mutex

	done := make(chan struct{})
	go func() {
		defer close(done)
		for {
			messageType, data, err := conn.ReadMessage()
			if err != nil {
				if gorillaws.IsCloseError(err, gorillaws.CloseNormalClosure) {
					mu.Lock()
					events = append(events, "CLOSE_RECEIVED")
					mu.Unlock()
				}
				return
			}

			if messageType == gorillaws.BinaryMessage && len(data) > 0 {
				stream := StreamID(data[0])
				mu.Lock()
				switch stream {
				case StreamStdout:
					events = append(events, "STDOUT")
				case StreamStderr:
					events = append(events, "STDERR")
				case StreamExit:
					events = append(events, "EXIT")
				}
				mu.Unlock()
			}
		}
	}()

	<-done

	// Verify sequence
	mu.Lock()
	defer mu.Unlock()

	t.Logf("Event sequence: %v", events)

	// Should have stdout before exit
	stdoutIndex := -1
	exitIndex := -1
	closeIndex := -1

	for i, event := range events {
		switch event {
		case "STDOUT":
			stdoutIndex = i
		case "EXIT":
			exitIndex = i
		case "CLOSE_RECEIVED":
			closeIndex = i
		}
	}

	if stdoutIndex == -1 {
		t.Error("stdout was not received")
	}
	if exitIndex == -1 {
		t.Error("exit was not received")
	}
	if closeIndex == -1 {
		t.Error("close was not received")
	}

	// Verify order
	if stdoutIndex > exitIndex {
		t.Error("stdout came after exit code")
	}
	if exitIndex > closeIndex {
		t.Error("exit code came after close")
	}
} 