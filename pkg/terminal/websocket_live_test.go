package terminal

import (
	"crypto/tls"
	"fmt"
	"net/http"
	"os"
	"strings"
	"sync"
	"testing"
	"time"

	gorillaws "github.com/gorilla/websocket"
)

// TestWebSocketLiveEnvironment tests against the actual sprite environment
// to detect the race condition where exit code arrives before stdout/stderr
func TestWebSocketLiveEnvironment(t *testing.T) {
	// Get environment variables
	spriteURL := os.Getenv("SPRITE_URL")
	spriteToken := os.Getenv("SPRITE_TOKEN")

	if spriteURL == "" || spriteToken == "" {
		t.Skip("SPRITE_URL and SPRITE_TOKEN environment variables not set")
	}

	// Parse the sprite URL to get base URL and sprite name
	// Expected format: https://sprite-env-prime.fly.dev/v1/sprites/prime
	parts := strings.Split(spriteURL, "/")
	if len(parts) < 6 {
		t.Fatalf("Invalid SPRITE_URL format: %s", spriteURL)
	}

	baseURL := strings.Join(parts[:3], "/") // https://sprite-env-prime.fly.dev
	spriteName := parts[len(parts)-1]       // prime

	t.Logf("Testing against live environment:")
	t.Logf("  Base URL: %s", baseURL)
	t.Logf("  Sprite: %s", spriteName)

	testCases := []struct {
		name       string
		command    []string
		expectOut  string
		iterations int
	}{
		{
			name:       "echo_test123",
			command:    []string{"echo", "test123"},
			expectOut:  "test123\n",
			iterations: 20,
		},
		{
			name:       "printf_no_newline",
			command:    []string{"sh", "-c", "printf 'test'"},
			expectOut:  "test",
			iterations: 20,
		},
		{
			name:       "fast_exit",
			command:    []string{"sh", "-c", "echo quick && exit 0"},
			expectOut:  "quick\n",
			iterations: 20,
		},
		{
			name:       "single_char",
			command:    []string{"sh", "-c", "printf 'x'"},
			expectOut:  "x",
			iterations: 20,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			var (
				correctOrderCount int
				wrongOrderCount   int
				noOutputCount     int
				mu                sync.Mutex
			)

			for i := 0; i < tc.iterations; i++ {
				// Build WebSocket URL for exec endpoint
				wsURL := strings.Replace(baseURL, "https://", "wss://", 1)
				wsURL = fmt.Sprintf("%s/v1/sprites/%s/exec", wsURL, spriteName)

				// Add command parameters
				params := []string{}
				for _, arg := range tc.command {
					params = append(params, fmt.Sprintf("cmd[]=%s", arg))
				}
				if len(params) > 0 {
					wsURL += "?" + strings.Join(params, "&")
				}

				// Set up WebSocket dialer with auth header
				dialer := &gorillaws.Dialer{
					TLSClientConfig: &tls.Config{
						InsecureSkipVerify: false,
					},
					HandshakeTimeout: 5 * time.Second,
				}

				headers := http.Header{}
				headers.Add("Authorization", fmt.Sprintf("Bearer %s", spriteToken))

				// Connect to WebSocket
				conn, resp, err := dialer.Dial(wsURL, headers)
				if err != nil {
					if resp != nil {
						t.Logf("Connection failed with status %d", resp.StatusCode)
					}
					t.Fatalf("Failed to connect to WebSocket: %v", err)
				}

				// Track message order
				var messages []string
				var gotStdout bool
				var gotExit bool
				var stdoutBeforeExit bool
				var stdoutContent string
				done := make(chan struct{})

				go func() {
					defer close(done)
					for {
						conn.SetReadDeadline(time.Now().Add(2 * time.Second))
						messageType, data, err := conn.ReadMessage()
						if err != nil {
							return
						}

						if messageType == gorillaws.BinaryMessage && len(data) > 0 {
							stream := StreamID(data[0])
							payload := data[1:]

							switch stream {
							case StreamReady:
								messages = append(messages, "READY")
							case StreamStdout:
								if !gotExit {
									stdoutBeforeExit = true
								}
								gotStdout = true
								stdoutContent += string(payload)
								messages = append(messages, fmt.Sprintf("STDOUT:%q", string(payload)))
							case StreamStderr:
								messages = append(messages, fmt.Sprintf("STDERR:%q", string(payload)))
							case StreamExit:
								gotExit = true
								exitCode := 0
								if len(payload) > 0 {
									exitCode = int(payload[0])
								}
								messages = append(messages, fmt.Sprintf("EXIT:%d", exitCode))
								// Give a small window for any late messages
								go func() {
									time.Sleep(100 * time.Millisecond)
									conn.Close()
								}()
							}
						}
					}
				}()

				// Wait for completion
				select {
				case <-done:
				case <-time.After(3 * time.Second):
					conn.Close()
					t.Logf("Iteration %d: timeout waiting for response", i)
				}

				// Analyze results
				mu.Lock()
				if !gotStdout {
					noOutputCount++
					t.Logf("Iteration %d: NO OUTPUT RECEIVED", i)
					t.Logf("  Messages: %v", messages)
				} else if gotExit && !stdoutBeforeExit {
					wrongOrderCount++
					t.Logf("Iteration %d: WRONG ORDER - exit before stdout", i)
					t.Logf("  Messages: %v", messages)
				} else {
					correctOrderCount++
					// Verify content matches expected
					if stdoutContent != tc.expectOut {
						t.Logf("Iteration %d: Output mismatch - got %q, expected %q",
							i, stdoutContent, tc.expectOut)
					}
				}
				mu.Unlock()

				conn.Close()

				// Small delay between iterations to avoid overwhelming the server
				time.Sleep(50 * time.Millisecond)
			}

			// Report results
			t.Logf("Test results for %q after %d iterations:", tc.name, tc.iterations)
			t.Logf("  Correct order (stdout before exit): %d", correctOrderCount)
			t.Logf("  Wrong order (exit before stdout): %d", wrongOrderCount)
			t.Logf("  No output received: %d", noOutputCount)

			if wrongOrderCount > 0 || noOutputCount > 0 {
				t.Errorf("RACE CONDITION DETECTED in live environment: %d failures out of %d iterations (%.1f%% failure rate)",
					wrongOrderCount+noOutputCount, tc.iterations,
					float64(wrongOrderCount+noOutputCount)*100/float64(tc.iterations))
			}
		})
	}
}

// TestWebSocketLiveSingleCommand tests a single command against the live environment
// with detailed logging to help diagnose the issue
func TestWebSocketLiveSingleCommand(t *testing.T) {
	// Get environment variables
	spriteURL := os.Getenv("SPRITE_URL")
	spriteToken := os.Getenv("SPRITE_TOKEN")

	if spriteURL == "" || spriteToken == "" {
		t.Skip("SPRITE_URL and SPRITE_TOKEN environment variables not set")
	}

	// Parse the sprite URL
	parts := strings.Split(spriteURL, "/")
	if len(parts) < 6 {
		t.Fatalf("Invalid SPRITE_URL format: %s", spriteURL)
	}

	baseURL := strings.Join(parts[:3], "/")
	spriteName := parts[len(parts)-1]

	// Build WebSocket URL for exec endpoint
	wsURL := strings.Replace(baseURL, "https://", "wss://", 1)
	wsURL = fmt.Sprintf("%s/v1/sprites/%s/exec?cmd[]=echo&cmd[]=test123", wsURL, spriteName)

	t.Logf("Connecting to: %s", wsURL)

	// Set up WebSocket dialer
	dialer := &gorillaws.Dialer{
		TLSClientConfig: &tls.Config{
			InsecureSkipVerify: false,
		},
		HandshakeTimeout: 5 * time.Second,
	}

	headers := http.Header{}
	headers.Add("Authorization", fmt.Sprintf("Bearer %s", spriteToken))

	// Connect
	conn, resp, err := dialer.Dial(wsURL, headers)
	if err != nil {
		if resp != nil {
			t.Logf("Connection failed with status %d", resp.StatusCode)
		}
		t.Fatalf("Failed to connect: %v", err)
	}
	defer conn.Close()

	t.Log("Connected successfully")

	// Track all messages with timestamps
	type messageInfo struct {
		time    time.Time
		msgType string
		data    string
	}
	var messages []messageInfo
	startTime := time.Now()
	done := make(chan struct{})

	go func() {
		defer close(done)
		for {
			conn.SetReadDeadline(time.Now().Add(3 * time.Second))
			messageType, data, err := conn.ReadMessage()
			if err != nil {
				t.Logf("Read error: %v", err)
				return
			}

			msg := messageInfo{
				time: time.Now(),
			}

			if messageType == gorillaws.BinaryMessage && len(data) > 0 {
				stream := StreamID(data[0])
				payload := data[1:]

				switch stream {
				case StreamReady:
					msg.msgType = "READY"
					msg.data = ""
				case StreamStdout:
					msg.msgType = "STDOUT"
					msg.data = string(payload)
				case StreamStderr:
					msg.msgType = "STDERR"
					msg.data = string(payload)
				case StreamExit:
					msg.msgType = "EXIT"
					if len(payload) > 0 {
						msg.data = fmt.Sprintf("code=%d", int(payload[0]))
					} else {
						msg.data = "code=0"
					}
					messages = append(messages, msg)
					// Close after receiving exit
					time.Sleep(100 * time.Millisecond)
					return
				default:
					msg.msgType = fmt.Sprintf("UNKNOWN(0x%02x)", stream)
					msg.data = string(payload)
				}

				messages = append(messages, msg)
			} else if messageType == gorillaws.TextMessage {
				msg.msgType = "TEXT"
				msg.data = string(data)
				messages = append(messages, msg)
			}
		}
	}()

	// Wait for completion
	select {
	case <-done:
		t.Log("Connection closed normally")
	case <-time.After(5 * time.Second):
		t.Log("Timeout waiting for response")
	}

	// Print detailed message log
	t.Log("Message sequence:")
	hasStdout := false
	hasExit := false
	for i, msg := range messages {
		elapsed := msg.time.Sub(startTime)
		t.Logf("  [%d] +%v %s: %q", i, elapsed, msg.msgType, msg.data)
		if msg.msgType == "STDOUT" {
			hasStdout = true
		}
		if msg.msgType == "EXIT" {
			hasExit = true
		}
	}

	if !hasStdout {
		t.Error("NO STDOUT RECEIVED from live environment!")
	}
	if !hasExit {
		t.Error("NO EXIT CODE RECEIVED from live environment!")
	}
	if hasStdout && hasExit {
		t.Log("✓ Both stdout and exit code received")
	}
}
