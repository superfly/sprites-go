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
		{
			name:          "slow_client_large_output",
			command:       []string{"sh", "-c", "for i in $(seq 1 200); do echo line $i with some padding to make it longer; done"},
			readDelay:     10 * time.Millisecond, // Slow reader
			readBatchSize: 5,
			expectedLines: 200,
		},
		{
			name:          "very_slow_client_burst_output",
			command:       []string{"sh", "-c", "for i in $(seq 1 150); do printf 'burst line %d\\n' $i; done"}, // Fast output
			readDelay:     100 * time.Millisecond,                                                               // Very slow reader - should cause backpressure
			readBatchSize: 1,
			expectedLines: 150,
		},
		{
			name:          "slow_client_with_stderr",
			command:       []string{"sh", "-c", "for i in $(seq 1 50); do echo stdout $i; echo stderr $i >&2; done"},
			readDelay:     20 * time.Millisecond,
			readBatchSize: 2,
			expectedLines: 100, // 50 stdout + 50 stderr
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			start := time.Now()
			t.Logf("[TEST START] %s - readDelay=%v, batchSize=%d, expectedLines=%d", tt.name, tt.readDelay, tt.readBatchSize, tt.expectedLines)
			t.Logf("[COMMAND] %v", tt.command)

			// Set up WebSocket server
			mux := http.NewServeMux()
			session := NewSession(
				WithCommand(tt.command[0], tt.command[1:]...),
				WithTTY(false),
			)
			handler := &WebSocketHandler{session: session}
			t.Logf("[SETUP] WebSocket server created with command: %v", tt.command)

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
			t.Logf("[CONNECT] Dialing WebSocket at %s", wsURL)
			conn, _, err := gorillaws.DefaultDialer.Dial(wsURL, nil)
			require.NoError(t, err)
			defer conn.Close()
			t.Logf("[CONNECT] WebSocket connection established at %v", time.Since(start))

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
			allMessages := []string{} // Track all messages for debugging
			t.Logf("[READER] Starting slow reader goroutine")
			go func() {
				defer close(done)
				defer t.Logf("[READER] Goroutine exiting with %d total messages read", messagesRead)

				iterationCount := 0
				for {
					iterationCount++
					// Don't delay on first iteration to catch early messages
					if iterationCount > 1 {
						// Simulate slow client by delaying reads
						t.Logf("[READER] Iteration %d: sleeping for %v before reading batch", iterationCount, tt.readDelay)
						time.Sleep(tt.readDelay)
					} else {
						t.Logf("[READER] Iteration 1: reading immediately without delay")
					}

					// Read a batch of messages
					t.Logf("[READER] Reading batch of %d messages", tt.readBatchSize)
					for i := 0; i < tt.readBatchSize; i++ {
						t.Logf("[READER] About to call ReadMessage for message %d of batch (total #%d)...", i+1, messagesRead+1)
						readStart := time.Now()
						messageType, data, err := conn.ReadMessage()
						readDuration := time.Since(readStart)
						messagesRead++
						t.Logf("[READER] ReadMessage returned after %v: messageType=%d, len(data)=%d, err=%v", readDuration, messageType, len(data), err)
						if err != nil {
							if gorillaws.IsCloseError(err, gorillaws.CloseNormalClosure) {
								mu.Lock()
								linesCount := len(receivedLines)
								closeReceived = true
								mu.Unlock()
								t.Logf("[%s] NORMAL CLOSE after %d messages, %d lines collected, exitReceived=%v", time.Since(start), messagesRead, linesCount, exitReceived)
								return
							}
							t.Logf("[%s] READ ERROR after %d messages: %v (type: %T)", time.Since(start), messagesRead, err, err)
							return
						}

						// Store message info for debugging
						msgInfo := fmt.Sprintf("MSG#%d: type=%s, bytes=%d", messagesRead, getMessageTypeName(messageType), len(data))
						if messageType == gorillaws.BinaryMessage && len(data) > 0 {
							streamID := StreamID(data[0])
							msgInfo += fmt.Sprintf(", streamID=%d", streamID)
						}
						allMessages = append(allMessages, msgInfo)

						t.Logf("[%s] MSG #%d: type=%d (%s), bytes=%d", time.Since(start), messagesRead, messageType, getMessageTypeName(messageType), len(data))

						if messageType == gorillaws.CloseMessage {
							mu.Lock()
							linesCount := len(receivedLines)
							closeReceived = true
							mu.Unlock()
							t.Logf("[%s] CLOSE FRAME after %d messages, %d lines collected, exitReceived=%v", time.Since(start), messagesRead, linesCount, exitReceived)
							t.Logf("[READER] All messages received: %v", allMessages)
							return
						}

						if messageType == gorillaws.BinaryMessage && len(data) > 0 {
							t.Logf("[READER] Processing binary message with %d bytes", len(data))
							streamID := StreamID(data[0])
							content := data[1:]
							t.Logf("[READER] StreamID=%d, content length=%d", streamID, len(content))

							switch streamID {
							case StreamStdout, StreamStderr:
								trimmed := strings.TrimSpace(string(content))
								if trimmed == "" {
									t.Logf("[%s] EMPTY content received on stream %d", time.Since(start), streamID)
									break
								}
								lines := strings.Split(trimmed, "\n")
								mu.Lock()
								prevTotal := len(receivedLines)
								receivedLines = append(receivedLines, lines...)
								newTotal := len(receivedLines)
								mu.Unlock()
								streamName := "stdout"
								if streamID == StreamStderr {
									streamName = "stderr"
								}
								preview := string(content)
								if len(preview) > 80 {
									preview = preview[:80] + "..."
								}
								t.Logf("[%s] %s: %d new lines (%d->%d total). Content: %q", time.Since(start), streamName, len(lines), prevTotal, newTotal, preview)
							case StreamExit:
								mu.Lock()
								exitReceived = true
								linesCount := len(receivedLines)
								mu.Unlock()
								exitCode := "unknown"
								if len(content) >= 1 {
									exitCode = fmt.Sprintf("%d", content[0])
								}
								t.Logf("[%s] EXIT received with code %s after %d lines collected", time.Since(start), exitCode, linesCount)
							case StreamReady:
								t.Logf("[%s] READY signal received - session is ready", time.Since(start))
							case StreamResize:
								t.Logf("[%s] RESIZE event received", time.Since(start))
							case StreamStdinEOF:
								t.Logf("[%s] STDIN EOF received", time.Since(start))
							default:
								t.Logf("[%s] UNKNOWN stream ID: %d", time.Since(start), streamID)
							}
							t.Logf("[READER] Finished processing binary message")
						} else if messageType == gorillaws.BinaryMessage {
							t.Logf("[READER] Binary message with 0 bytes")
						} else {
							t.Logf("[READER] Non-binary message type: %d", messageType)
						}

						t.Logf("[READER] Message %d processing complete, continuing to next message in batch", i+1)
					}
					t.Logf("[READER] Batch read complete, going to next iteration")
				}
			}()

			// Give reader a moment to start, then send EOF to stdin
			time.Sleep(10 * time.Millisecond)
			eofMessage := []byte{byte(StreamStdinEOF)}
			t.Logf("[SEND] Sending stdin EOF signal")
			err = conn.WriteMessage(gorillaws.BinaryMessage, eofMessage)
			require.NoError(t, err)
			t.Logf("[SEND] Stdin EOF sent successfully")

			// Wait for reading to complete or timeout
			t.Logf("[WAIT] Waiting for reader to complete (timeout: 60s)")
			select {
			case <-done:
				t.Logf("[WAIT] Reader finished after %v", time.Since(start))
			case <-time.After(60 * time.Second): // Increased timeout for slow clients
				if !tt.expectTimeout {
					mu.Lock()
					linesCount := len(receivedLines)
					mu.Unlock()
					t.Fatalf("[%s] TEST TIMEOUT - slow client couldn't keep up (messagesRead=%d, linesCollected=%d, exitReceived=%v, closeReceived=%v)",
						time.Since(start), messagesRead, linesCount, exitReceived, closeReceived)
				}
				t.Logf("[WAIT] Timeout as expected")
			}

			// Verify results
			mu.Lock()
			totalLines := len(receivedLines)
			mu.Unlock()

			t.Logf("[VERIFY] Final stats: totalLines=%d (expected=%d), exitReceived=%v, closeReceived=%v, messagesRead=%d",
				totalLines, tt.expectedLines, exitReceived, closeReceived, messagesRead)

			if totalLines != tt.expectedLines {
				t.Logf("[VERIFY] Line count mismatch. Received lines:")
				for i, line := range receivedLines {
					t.Logf("  [%d]: %q", i+1, line)
				}
			}

			assert.Equal(t, tt.expectedLines, totalLines, "Should receive all lines even with slow client")
			assert.True(t, exitReceived, "Should receive exit code")
			assert.True(t, closeReceived, "Should receive close frame")

			// Verify no data was lost
			if tt.name == "slow_client_small_output" {
				t.Logf("[VERIFY] Checking for specific expected lines")
				for i := 1; i <= 5; i++ {
					expected := fmt.Sprintf("line %d", i)
					found := false
					for _, line := range receivedLines {
						if line == expected {
							found = true
							break
						}
					}
					if !found {
						t.Logf("[VERIFY] Missing expected line: %q", expected)
					}
					assert.Contains(t, receivedLines, expected, "Should not lose any output lines")
				}
			}

			t.Logf("[TEST END] %s completed in %v", tt.name, time.Since(start))
		})
	}
}

// Helper function to get message type name
func getMessageTypeName(messageType int) string {
	switch messageType {
	case gorillaws.TextMessage:
		return "TextMessage"
	case gorillaws.BinaryMessage:
		return "BinaryMessage"
	case gorillaws.CloseMessage:
		return "CloseMessage"
	case gorillaws.PingMessage:
		return "PingMessage"
	case gorillaws.PongMessage:
		return "PongMessage"
	default:
		return fmt.Sprintf("Unknown(%d)", messageType)
	}
}
