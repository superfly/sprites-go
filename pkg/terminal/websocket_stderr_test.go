package terminal

import (
	"encoding/json"
	"fmt"
	"net/http"
	"net/http/httptest"
	"strings"
	"sync"
	"testing"
	"time"

	gorillaws "github.com/gorilla/websocket"
)

// TestWebSocketStderrCapture specifically tests stderr capture issue
func TestWebSocketStderrCapture(t *testing.T) {
	testCases := []struct {
		name           string
		command        []string
		expectStdout   string
		expectStderr   string
		expectExitCode int
	}{
		{
			name:           "stderr only",
			command:        []string{"sh", "-c", "echo 'error message' >&2"},
			expectStdout:   "",
			expectStderr:   "error message\n",
			expectExitCode: 0,
		},
		{
			name:           "both stdout and stderr",
			command:        []string{"sh", "-c", "echo stdout && echo stderr >&2"},
			expectStdout:   "stdout\n",
			expectStderr:   "stderr\n",
			expectExitCode: 0,
		},
		{
			name:           "large stderr output",
			command:        []string{"sh", "-c", "for i in $(seq 1 100); do echo \"error$i\" >&2; done"},
			expectStdout:   "",
			expectStderr:   "error100", // Check if contains this
			expectExitCode: 0,
		},
		{
			name:           "stderr with non-zero exit",
			command:        []string{"sh", "-c", "echo 'failure' >&2; exit 1"},
			expectStdout:   "",
			expectStderr:   "failure\n",
			expectExitCode: 1,
		},
		{
			name:           "immediate exit after stderr",
			command:        []string{"sh", "-c", "echo 'quick' >&2; exit 0"},
			expectStdout:   "",
			expectStderr:   "quick\n",
			expectExitCode: 0,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			// Create session
			session := NewSession(
				WithCommand(tc.command[0], tc.command[1:]...),
				WithTTY(false), // Important: non-TTY mode to test separate streams
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
			receivedStreams := make(map[StreamID][]byte)
			var exitCode int
			exitCodeReceived := false
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

						mu.Lock()
						switch stream {
						case StreamStdout:
							receivedStreams[StreamStdout] = append(receivedStreams[StreamStdout], payload...)
						case StreamStderr:
							receivedStreams[StreamStderr] = append(receivedStreams[StreamStderr], payload...)
						case StreamExit:
							if len(payload) > 0 {
								exitCode = int(payload[0])
								exitCodeReceived = true
							}
							mu.Unlock()
							return
						}
						mu.Unlock()
					}
				}
			}()

			// Wait for completion with timeout
			select {
			case <-done:
				// Normal completion
			case <-time.After(5 * time.Second):
				t.Fatal("test timeout")
			}

			// Verify results
			mu.Lock()
			defer mu.Unlock()

			if !exitCodeReceived {
				t.Error("exit code was not received")
			} else if exitCode != tc.expectExitCode {
				t.Errorf("expected exit code %d, got %d", tc.expectExitCode, exitCode)
			}

			// Check stdout
			stdout := string(receivedStreams[StreamStdout])
			if stdout != tc.expectStdout {
				t.Errorf("stdout mismatch:\nexpected: %q\ngot: %q", tc.expectStdout, stdout)
			}

			// Check stderr
			stderr := string(receivedStreams[StreamStderr])
			if tc.expectStderr != "" {
				if strings.Contains(tc.expectStderr, "error100") {
					// For large output test, just check if it contains the last line
					if !strings.Contains(stderr, tc.expectStderr) {
						t.Errorf("stderr missing expected content %q, got: %q", tc.expectStderr, stderr)
					}
				} else if stderr != tc.expectStderr {
					t.Errorf("stderr mismatch:\nexpected: %q\ngot: %q", tc.expectStderr, stderr)
				}
			}

			// Log what we received for debugging
			t.Logf("Received streams: stdout=%d bytes, stderr=%d bytes",
				len(receivedStreams[StreamStdout]), len(receivedStreams[StreamStderr]))
		})
	}
}

// TestWebSocketStderrRaceCondition tests the specific race condition with fast-exiting commands
func TestWebSocketStderrRaceCondition(t *testing.T) {
	// Run the test multiple times to catch race conditions
	for i := 0; i < 10; i++ {
		t.Run(fmt.Sprintf("iteration_%d", i), func(t *testing.T) {
			// Command that writes to stderr and exits immediately
			session := NewSession(
				WithCommand("sh", "-c", "echo 'race test' >&2"),
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

			stderrReceived := false
			exitReceived := false
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
						switch stream {
						case StreamStderr:
							stderrReceived = true
						case StreamExit:
							exitReceived = true
							// Give a small window for any pending messages
							time.Sleep(10 * time.Millisecond)
							return
						}
					}
				}
			}()

			select {
			case <-done:
			case <-time.After(2 * time.Second):
				t.Fatal("timeout waiting for completion")
			}

			if !exitReceived {
				t.Error("exit code not received")
			}
			if !stderrReceived {
				t.Error("stderr not received - race condition detected!")
			}
		})
	}
}

// TestWebSocketFlushEffectiveness tests if the flush mechanism works properly
func TestWebSocketFlushEffectiveness(t *testing.T) {
	// Create a command that outputs to stderr and exits
	session := NewSession(
		WithCommand("sh", "-c", "for i in 1 2 3; do echo \"line$i\" >&2; done"),
		WithTTY(false),
	)

	handler := NewWebSocketHandler(session)

	// Wrap the handler to track flush behavior
	instrumentedHandler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		// We need to instrument the flush call somehow
		// For now, just run the normal handler
		if err := handler.Handle(w, r); err != nil {
			t.Errorf("handler error: %v", err)
		}
	})

	server := httptest.NewServer(instrumentedHandler)
	defer server.Close()

	wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
	dialer := gorillaws.DefaultDialer
	conn, _, err := dialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("failed to connect: %v", err)
	}
	defer conn.Close()

	var stderrLines []string
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
				case StreamStderr:
					lines := strings.Split(strings.TrimSpace(string(payload)), "\n")
					for _, line := range lines {
						if line != "" {
							stderrLines = append(stderrLines, line)
						}
					}
				case StreamExit:
					return
				}
			}
		}
	}()

	select {
	case <-done:
	case <-time.After(3 * time.Second):
		t.Fatal("timeout")
	}

	// Should have received all 3 lines
	if len(stderrLines) != 3 {
		t.Errorf("expected 3 stderr lines, got %d: %v", len(stderrLines), stderrLines)
	}
}

// TestWebSocketStderrWithTextMessages tests stderr handling when text messages are also sent
func TestWebSocketStderrWithTextMessages(t *testing.T) {
	session := NewSession(
		WithCommand("sh", "-c", "echo 'stderr output' >&2"),
		WithTTY(false),
	)

	handler := NewWebSocketHandler(session).WithOnConnected(func(sender TextMessageSender) {
		// Send a text message when connected
		msg := map[string]string{"type": "connected", "message": "WebSocket connected"}
		data, _ := json.Marshal(msg)
		sender.SendTextMessage(data)
	})

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

	var textMessageReceived bool
	var stderrReceived bool
	done := make(chan struct{})

	go func() {
		defer close(done)
		for {
			messageType, data, err := conn.ReadMessage()
			if err != nil {
				return
			}

			switch messageType {
			case gorillaws.TextMessage:
				textMessageReceived = true
			case gorillaws.BinaryMessage:
				if len(data) > 0 {
					stream := StreamID(data[0])
					switch stream {
					case StreamStderr:
						stderrReceived = true
					case StreamExit:
						return
					}
				}
			}
		}
	}()

	select {
	case <-done:
	case <-time.After(2 * time.Second):
		t.Fatal("timeout")
	}

	if !textMessageReceived {
		t.Error("text message not received")
	}
	if !stderrReceived {
		t.Error("stderr not received")
	}
}
