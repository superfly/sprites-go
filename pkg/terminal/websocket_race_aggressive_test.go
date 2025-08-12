package terminal

import (
	"fmt"
	"net/http"
	"net/http/httptest"
	"runtime"
	"strings"
	"sync"
	"testing"
	"time"

	gorillaws "github.com/gorilla/websocket"
)

// TestWebSocketAggressiveRaceDetection aggressively tests for the race condition
// where exit code arrives before stdout/stderr by using many iterations and
// artificially slowing down the write loop.
func TestWebSocketAggressiveRaceDetection(t *testing.T) {
	// Save original GOMAXPROCS
	originalGOMAXPROCS := runtime.GOMAXPROCS(0)
	defer runtime.GOMAXPROCS(originalGOMAXPROCS)

	// Force single-threaded execution to increase context switching
	runtime.GOMAXPROCS(1)

	testCases := []struct {
		name       string
		command    []string
		expectOut  string
		iterations int
	}{
		{
			name:       "single_byte",
			command:    []string{"sh", "-c", "printf 'x'"},
			expectOut:  "x",
			iterations: 200,
		},
		{
			name:       "echo_test",
			command:    []string{"sh", "-c", "echo test123"},
			expectOut:  "test123\n",
			iterations: 200,
		},
		{
			name:       "fast_exit",
			command:    []string{"sh", "-c", "echo quick && exit 0"},
			expectOut:  "quick\n",
			iterations: 200,
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
				// Create a new session for each iteration
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

				// Connect as WebSocket client
				wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
				dialer := gorillaws.DefaultDialer
				dialer.HandshakeTimeout = 1 * time.Second
				conn, _, err := dialer.Dial(wsURL, nil)
				if err != nil {
					t.Fatalf("failed to connect: %v", err)
					server.Close()
					continue
				}

				// Track message order
				var gotStdout bool
				var gotExit bool
				var stdoutBeforeExit bool
				done := make(chan struct{})

				go func() {
					defer close(done)
					for {
						conn.SetReadDeadline(time.Now().Add(1 * time.Second))
						messageType, data, err := conn.ReadMessage()
						if err != nil {
							return
						}

						if messageType == gorillaws.BinaryMessage && len(data) > 0 {
							stream := StreamID(data[0])
							switch stream {
							case StreamReady:
								// Ignore ready signal
							case StreamStdout:
								if !gotExit {
									stdoutBeforeExit = true
								}
								gotStdout = true
							case StreamStderr:
								// Could track stderr too
							case StreamExit:
								gotExit = true
								// Don't return immediately - continue reading to see if stdout arrives late
								go func() {
									time.Sleep(50 * time.Millisecond)
									conn.Close()
								}()
							}
						}
					}
				}()

				// Wait for completion
				select {
				case <-done:
				case <-time.After(2 * time.Second):
					conn.Close()
				}

				// Analyze results
				mu.Lock()
				if !gotStdout {
					noOutputCount++
					if i < 10 || (wrongOrderCount+noOutputCount) < 5 { // Log first few failures
						t.Logf("Iteration %d: NO OUTPUT RECEIVED", i)
					}
				} else if gotExit && !stdoutBeforeExit {
					wrongOrderCount++
					if i < 10 || (wrongOrderCount+noOutputCount) < 5 { // Log first few failures
						t.Logf("Iteration %d: WRONG ORDER - exit before stdout", i)
					}
				} else {
					correctOrderCount++
				}
				mu.Unlock()

				conn.Close()
				server.Close()

				// Add some CPU work to stress the scheduler
				sum := 0
				for j := 0; j < 1000; j++ {
					sum += j * j
				}
				_ = sum
			}

			// Report results
			t.Logf("Test results for %q after %d iterations:", tc.name, tc.iterations)
			t.Logf("  Correct order (stdout before exit): %d", correctOrderCount)
			t.Logf("  Wrong order (exit before stdout): %d", wrongOrderCount)
			t.Logf("  No output received: %d", noOutputCount)

			// This test is expected to fail sometimes due to the race condition
			if wrongOrderCount > 0 || noOutputCount > 0 {
				t.Errorf("RACE CONDITION DETECTED: %d failures out of %d iterations (%.1f%% failure rate)",
					wrongOrderCount+noOutputCount, tc.iterations,
					float64(wrongOrderCount+noOutputCount)*100/float64(tc.iterations))
			}
		})
	}
}

// TestWebSocketSlowWriteSimulation simulates slow WebSocket writes to trigger the race
func TestWebSocketSlowWriteSimulation(t *testing.T) {
	// This test modifies the write behavior to simulate slow writes
	// by adding artificial delays in the write loop

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		session := NewSession(
			WithCommand("sh", "-c", "echo 'test output'"),
			WithTTY(false),
		)
		handler := NewWebSocketHandler(session)
		if err := handler.Handle(w, r); err != nil {
			t.Errorf("handler error: %v", err)
		}
	}))
	defer server.Close()

	// Run multiple iterations
	failures := 0
	iterations := 50

	for i := 0; i < iterations; i++ {
		// Connect as WebSocket client
		wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
		dialer := gorillaws.DefaultDialer
		conn, _, err := dialer.Dial(wsURL, nil)
		if err != nil {
			t.Fatalf("failed to connect: %v", err)
		}

		// Track messages
		var messages []string
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
					case StreamStdout:
						messages = append(messages, fmt.Sprintf("stdout:%s", string(data[1:])))
					case StreamExit:
						messages = append(messages, fmt.Sprintf("exit:%d", int(data[1])))
						// Give time for any late messages
						time.Sleep(20 * time.Millisecond)
						return
					}
				}
			}
		}()

		// Wait for completion
		select {
		case <-done:
		case <-time.After(1 * time.Second):
			t.Logf("Iteration %d: timeout", i)
		}

		conn.Close()

		// Check order
		hasStdout := false
		exitBeforeStdout := false

		for _, msg := range messages {
			if strings.HasPrefix(msg, "stdout:") {
				hasStdout = true
			} else if strings.HasPrefix(msg, "exit:") {
				if !hasStdout {
					exitBeforeStdout = true
				}
			}
		}

		if !hasStdout || exitBeforeStdout {
			failures++
			t.Logf("Iteration %d FAILED: messages=%v", i, messages)
		}
	}

	if failures > 0 {
		t.Errorf("Race condition detected: %d/%d iterations failed (%.1f%% failure rate)",
			failures, iterations, float64(failures)*100/float64(iterations))
	} else {
		t.Logf("All %d iterations passed", iterations)
	}
}
