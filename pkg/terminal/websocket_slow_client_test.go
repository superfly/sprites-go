package terminal

import (
	"fmt"
	"net/http"
	"net/http/httptest"
	"strings"
	"sync"
	"testing"
	"time"

	gorillaws "github.com/gorilla/websocket"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestWebSocketSlowClient tests that a slow client can still receive all data
// even when the server produces output faster than the client can read
func TestWebSocketSlowClient(t *testing.T) {
	tests := []struct {
		name          string
		command       []string
		readDelay     time.Duration // How long client waits between reads
		readBatchSize int           // How many messages to read at once
		expectedLines int
		expectTimeout bool
	}{
		{
			name:          "slow_client_small_output",
			command:       []string{"sh", "-c", "for i in 1 2 3 4 5; do echo line $i; done"},
			readDelay:     100 * time.Millisecond, // Very slow reader
			readBatchSize: 1,
			expectedLines: 5,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Set up WebSocket server
			mux := http.NewServeMux()
			session := NewSession()
			handler := &WebSocketHandler{session: session}

			// Create wrapper to handle error return
			mux.HandleFunc("/exec", func(w http.ResponseWriter, r *http.Request) {
				if err := handler.Handle(w, r); err != nil {
					http.Error(w, err.Error(), http.StatusInternalServerError)
				}
			})
			server := httptest.NewServer(mux)
			defer server.Close()

			// Connect slow client
			wsURL := strings.Replace(server.URL, "http://", "ws://", 1) + "/exec"
			conn, _, err := gorillaws.DefaultDialer.Dial(wsURL, nil)
			require.NoError(t, err)
			defer conn.Close()

			// Start command
			cmd := map[string]interface{}{
				"command": tt.command,
			}
			err = conn.WriteJSON(cmd)
			require.NoError(t, err)

			// Slow client reader
			var (
				mu            sync.Mutex
				receivedLines []string
				exitReceived  bool
				closeReceived bool
			)

			// Read messages slowly
			done := make(chan struct{})
			messagesRead := 0
			go func() {
				defer close(done)

				for {
					// Simulate slow client by delaying reads
					time.Sleep(tt.readDelay)

					// Read a batch of messages
					for i := 0; i < tt.readBatchSize; i++ {
						messageType, data, err := conn.ReadMessage()
						messagesRead++
						if err != nil {
							if gorillaws.IsCloseError(err, gorillaws.CloseNormalClosure) {
								mu.Lock()
								closeReceived = true
								mu.Unlock()
								t.Logf("Connection closed normally after %d messages, %d lines", messagesRead, len(receivedLines))
								return
							}
							t.Logf("Read error after %d messages: %v", messagesRead, err)
							return
						}

						if messageType == gorillaws.CloseMessage {
							mu.Lock()
							closeReceived = true
							mu.Unlock()
							t.Logf("Received close message after %d messages", messagesRead)
							return
						}

						if messageType == gorillaws.BinaryMessage && len(data) > 0 {
							streamID := StreamID(data[0])
							content := data[1:]

							switch streamID {
							case StreamStdout, StreamStderr:
								lines := strings.Split(strings.TrimSpace(string(content)), "\n")
								mu.Lock()
								receivedLines = append(receivedLines, lines...)
								mu.Unlock()
								t.Logf("Received %d lines (total: %d)", len(lines), len(receivedLines))
							case StreamExit:
								mu.Lock()
								exitReceived = true
								mu.Unlock()
								t.Logf("Exit received after %d lines", len(receivedLines))
							}
						}
					}
				}
			}()

			// Wait for reading to complete or timeout
			select {
			case <-done:
				// Reader finished
			case <-time.After(10 * time.Second):
				if !tt.expectTimeout {
					t.Fatal("Test timed out - slow client couldn't keep up")
				}
			}

			// Verify results
			mu.Lock()
			totalLines := len(receivedLines)
			mu.Unlock()

			assert.Equal(t, tt.expectedLines, totalLines, "Should receive all lines even with slow client")
			assert.True(t, exitReceived, "Should receive exit code")
			assert.True(t, closeReceived, "Should receive close frame")

			// Verify no data was lost
			if tt.name == "slow_client_small_output" {
				for i := 1; i <= 10; i++ {
					expected := fmt.Sprintf("line %d", i)
					assert.Contains(t, receivedLines, expected, "Should not lose any output lines")
				}
			}
		})
	}
}
