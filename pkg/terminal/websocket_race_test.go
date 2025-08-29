package terminal

import (
	"fmt"
	"net/http"
	"net/http/httptest"
	"strings"
	"sync"
	"testing"
	"time"

	"runtime"

	gorillaws "github.com/gorilla/websocket"
)

// TestWebSocketMessageOrdering verifies that stdout/stderr messages are always
// received before the exit code message. This test is designed to catch the
// race condition where fast-exiting commands might send their exit code before
// their output has been transmitted.
func TestWebSocketMessageOrdering(t *testing.T) {
	testCases := []struct {
		name       string
		command    []string
		expectOut  string
		iterations int
	}{
		{
			name:       "echo_hello",
			command:    []string{"echo", "hello"},
			expectOut:  "hello\n",
			iterations: 100,
		},
		{
			name:       "printf_no_newline",
			command:    []string{"sh", "-c", "printf 'test'"},
			expectOut:  "test",
			iterations: 100,
		},
		{
			name:       "fast_exit_with_output",
			command:    []string{"sh", "-c", "echo 'quick output' && exit 0"},
			expectOut:  "quick output\n",
			iterations: 100,
		},
		{
			name:       "single_char_output",
			command:    []string{"sh", "-c", "printf 'x'"},
			expectOut:  "x",
			iterations: 100,
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
				defer server.Close()

				// Connect as WebSocket client
				wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
				dialer := gorillaws.DefaultDialer
				conn, _, err := dialer.Dial(wsURL, nil)
				if err != nil {
					t.Fatalf("failed to connect: %v", err)
				}
				defer conn.Close()

				// Track message order
				type messageEvent struct {
					msgType string // "stdout", "stderr", "exit"
					data    []byte
					time    time.Time
				}
				var events []messageEvent
				var eventsMu sync.Mutex

				done := make(chan struct{})
				go func() {
					defer close(done)
					for {
						messageType, data, err := conn.ReadMessage()
						if err != nil {
							if gorillaws.IsCloseError(err, gorillaws.CloseNormalClosure) {
								// Normal close
							}
							return
						}

						if messageType == gorillaws.BinaryMessage && len(data) > 0 {
							stream := StreamID(data[0])
							payload := data[1:]

							eventsMu.Lock()
							switch stream {
							case StreamReady:
								// Session ready signal - ignore for this test
							case StreamStdout:
								events = append(events, messageEvent{
									msgType: "stdout",
									data:    payload,
									time:    time.Now(),
								})
							case StreamStderr:
								events = append(events, messageEvent{
									msgType: "stderr",
									data:    payload,
									time:    time.Now(),
								})
							case StreamExit:
								var exitCode int
								if len(payload) > 0 {
									exitCode = int(payload[0])
								}
								events = append(events, messageEvent{
									msgType: "exit",
									data:    []byte(fmt.Sprintf("%d", exitCode)),
									time:    time.Now(),
								})
								eventsMu.Unlock()
								return
							}
							eventsMu.Unlock()
						}
					}
				}()

				// Wait for completion
				select {
				case <-done:
				case <-time.After(2 * time.Second):
					t.Fatal("timeout waiting for WebSocket data")
				}

				// Analyze the message order
				eventsMu.Lock()
				defer eventsMu.Unlock()

				// Find stdout and exit messages
				var stdoutIndex, exitIndex int = -1, -1
				var gotStdout string

				for i, event := range events {
					switch event.msgType {
					case "stdout":
						if stdoutIndex == -1 {
							stdoutIndex = i
						}
						gotStdout += string(event.data)
					case "exit":
						exitIndex = i
					}
				}

				mu.Lock()
				if stdoutIndex == -1 {
					// No stdout received at all
					noOutputCount++
					t.Logf("Iteration %d: NO OUTPUT - exit at index %d", i, exitIndex)
				} else if exitIndex != -1 && exitIndex < stdoutIndex {
					// Exit code came before stdout (wrong order)
					wrongOrderCount++
					t.Logf("Iteration %d: WRONG ORDER - exit at index %d, stdout at index %d",
						i, exitIndex, stdoutIndex)
				} else {
					// Correct order
					correctOrderCount++
					if gotStdout != tc.expectOut {
						t.Logf("Iteration %d: Output mismatch - got %q, expected %q",
							i, gotStdout, tc.expectOut)
					}
				}
				mu.Unlock()

				// Log all events for debugging
				if stdoutIndex == -1 || (exitIndex != -1 && exitIndex < stdoutIndex) {
					t.Logf("Iteration %d events:", i)
					for j, event := range events {
						if event.msgType == "stdout" || event.msgType == "stderr" {
							t.Logf("  [%d] %s: %q", j, event.msgType, string(event.data))
						} else {
							t.Logf("  [%d] %s", j, event.msgType)
						}
					}
				}
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

// TestWebSocketFlushEffectiveness tests whether the current flush mechanism
// is effective at ensuring all data is transmitted before the exit code
func TestWebSocketFlushEffectiveness(t *testing.T) {
	// Run a command that outputs data and exits quickly
	session := NewSession(
		WithCommand("sh", "-c", "echo 'test output'"),
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

	// Track all messages with timestamps
	type timedMessage struct {
		stream StreamID
		data   []byte
		time   time.Time
	}
	var messages []timedMessage
	var mu sync.Mutex

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
				messages = append(messages, timedMessage{
					stream: stream,
					data:   payload,
					time:   time.Now(),
				})
				mu.Unlock()

				if stream == StreamExit {
					// Continue reading to see if more data arrives
					time.Sleep(100 * time.Millisecond)
					return
				}
			}
		}
	}()

	<-done

	// Analyze the results
	mu.Lock()
	defer mu.Unlock()

	var stdoutFound, exitFound bool
	var stdoutTime, exitTime time.Time

	for _, msg := range messages {
		switch msg.stream {
		case StreamStdout:
			if !stdoutFound {
				stdoutFound = true
				stdoutTime = msg.time
			}
		case StreamExit:
			exitFound = true
			exitTime = msg.time
		}
	}

	if !stdoutFound {
		t.Error("stdout message was not received")
	}
	if !exitFound {
		t.Error("exit message was not received")
	}

	if stdoutFound && exitFound {
		if exitTime.Before(stdoutTime) {
			t.Errorf("exit message (at %v) arrived before stdout message (at %v)",
				exitTime.Format("15:04:05.000"), stdoutTime.Format("15:04:05.000"))
		} else {
			t.Logf("Correct order: stdout at %v, exit at %v (delta: %v)",
				stdoutTime.Format("15:04:05.000"),
				exitTime.Format("15:04:05.000"),
				exitTime.Sub(stdoutTime))
		}
	}

	// Log all messages for debugging
	t.Log("All messages received:")
	for i, msg := range messages {
		t.Logf("  [%d] Stream %d at %v: %q",
			i, msg.stream, msg.time.Format("15:04:05.000"), string(msg.data))
	}
}

// TestWebSocketRaceWithConcurrentClients simulates the race condition with
// multiple concurrent WebSocket clients to stress the server
func TestWebSocketRaceWithConcurrentClients(t *testing.T) {
	// Run the test with different numbers of concurrent clients
	concurrencyLevels := []int{5, 10, 20}

	for _, numClients := range concurrencyLevels {
		t.Run(fmt.Sprintf("concurrent_%d", numClients), func(t *testing.T) {
			server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
				// Create a new session for each request
				session := NewSession(
					WithCommand("echo", "hello"),
					WithTTY(false),
				)
				handler := NewWebSocketHandler(session)
				if err := handler.Handle(w, r); err != nil {
					t.Errorf("handler error: %v", err)
				}
			}))
			defer server.Close()

			var wg sync.WaitGroup
			results := make(chan string, numClients)

			// Launch concurrent clients
			for i := 0; i < numClients; i++ {
				wg.Add(1)
				go func(clientID int) {
					defer wg.Done()

					// Connect as WebSocket client
					wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
					dialer := gorillaws.DefaultDialer
					conn, _, err := dialer.Dial(wsURL, nil)
					if err != nil {
						results <- fmt.Sprintf("client %d: connection failed: %v", clientID, err)
						return
					}
					defer conn.Close()

					// Track message order
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
									messages = append(messages, "stdout")
								case StreamExit:
									messages = append(messages, "exit")
									return
								}
							}
						}
					}()

					// Wait for completion
					select {
					case <-done:
					case <-time.After(2 * time.Second):
						results <- fmt.Sprintf("client %d: timeout", clientID)
						return
					}

					// Check message order
					if len(messages) == 2 && messages[0] == "stdout" && messages[1] == "exit" {
						results <- fmt.Sprintf("client %d: correct order", clientID)
					} else if len(messages) == 2 && messages[0] == "exit" && messages[1] == "stdout" {
						results <- fmt.Sprintf("client %d: WRONG ORDER (exit before stdout)", clientID)
					} else if len(messages) == 1 && messages[0] == "exit" {
						results <- fmt.Sprintf("client %d: NO STDOUT received", clientID)
					} else {
						results <- fmt.Sprintf("client %d: unexpected messages: %v", clientID, messages)
					}
				}(i)
			}

			// Wait for all clients to complete
			wg.Wait()
			close(results)

			// Analyze results
			correctCount := 0
			wrongCount := 0
			var failures []string

			for result := range results {
				t.Logf("  %s", result)
				if strings.Contains(result, "correct order") {
					correctCount++
				} else {
					wrongCount++
					failures = append(failures, result)
				}
			}

			t.Logf("Summary: %d correct, %d wrong out of %d clients", correctCount, wrongCount, numClients)
			if wrongCount > 0 {
				t.Errorf("RACE CONDITION DETECTED with %d concurrent clients: %.1f%% failure rate",
					numClients, float64(wrongCount)*100/float64(numClients))
			}
		})
	}
}

// TestWebSocketSequentialClients tests multiple clients sequentially to compare with concurrent test
func TestWebSocketSequentialClients(t *testing.T) {
	// Run the test with different numbers of clients
	clientCounts := []int{5, 10, 20}

	for _, numClients := range clientCounts {
		t.Run(fmt.Sprintf("sequential_%d", numClients), func(t *testing.T) {
			server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
				// Create a new session for each request
				session := NewSession(
					WithCommand("echo", "hello"),
					WithTTY(false),
				)
				handler := NewWebSocketHandler(session)
				if err := handler.Handle(w, r); err != nil {
					t.Errorf("handler error: %v", err)
				}
			}))
			defer server.Close()

			results := []string{}

			// Launch clients SEQUENTIALLY
			for i := 0; i < numClients; i++ {
				// Connect as WebSocket client
				wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
				dialer := gorillaws.DefaultDialer
				conn, _, err := dialer.Dial(wsURL, nil)
				if err != nil {
					results = append(results, fmt.Sprintf("client %d: connection failed: %v", i, err))
					continue
				}

				// Track message order
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
								messages = append(messages, "stdout")
							case StreamExit:
								messages = append(messages, "exit")
								return
							}
						}
					}
				}()

				// Wait for completion
				select {
				case <-done:
				case <-time.After(2 * time.Second):
					results = append(results, fmt.Sprintf("client %d: timeout", i))
					conn.Close()
					continue
				}

				// Check message order
				if len(messages) == 2 && messages[0] == "stdout" && messages[1] == "exit" {
					results = append(results, fmt.Sprintf("client %d: correct order", i))
				} else if len(messages) == 2 && messages[0] == "exit" && messages[1] == "stdout" {
					results = append(results, fmt.Sprintf("client %d: WRONG ORDER (exit before stdout)", i))
				} else if len(messages) == 1 && messages[0] == "exit" {
					results = append(results, fmt.Sprintf("client %d: NO STDOUT received", i))
				} else {
					results = append(results, fmt.Sprintf("client %d: unexpected messages: %v", i, messages))
				}

				conn.Close()
			}

			// Analyze results
			correctCount := 0
			wrongCount := 0

			for _, result := range results {
				t.Logf("  %s", result)
				if strings.Contains(result, "correct order") {
					correctCount++
				} else {
					wrongCount++
				}
			}

			t.Logf("Summary: %d correct, %d wrong out of %d clients", correctCount, wrongCount, numClients)
			if wrongCount > 0 {
				t.Errorf("RACE CONDITION DETECTED with %d sequential clients: %.1f%% failure rate",
					numClients, float64(wrongCount)*100/float64(numClients))
			}
		})
	}
}

// TestWebSocketSimpleEcho tests a simple echo command to debug the race condition
func TestWebSocketSimpleEcho(t *testing.T) {
	for i := 0; i < 10; i++ {
		t.Run(fmt.Sprintf("iteration_%d", i), func(t *testing.T) {
			// Create session
			session := NewSession(
				WithCommand("echo", "hello"),
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

			// Track all messages
			var messages []string
			done := make(chan struct{})

			go func() {
				defer close(done)
				for {
					messageType, data, err := conn.ReadMessage()
					if err != nil {
						if gorillaws.IsCloseError(err, gorillaws.CloseNormalClosure) {
							messages = append(messages, "CLOSE")
						}
						return
					}

					if messageType == gorillaws.BinaryMessage && len(data) > 0 {
						stream := StreamID(data[0])
						payload := data[1:]

						switch stream {
						case StreamStdout:
							messages = append(messages, fmt.Sprintf("STDOUT: %q", string(payload)))
						case StreamStderr:
							messages = append(messages, fmt.Sprintf("STDERR: %q", string(payload)))
						case StreamExit:
							var exitCode int
							if len(payload) > 0 {
								exitCode = int(payload[0])
							}
							messages = append(messages, fmt.Sprintf("EXIT: %d", exitCode))
						}
					}
				}
			}()

			// Wait for completion
			select {
			case <-done:
			case <-time.After(2 * time.Second):
				t.Fatal("timeout")
			}

			// Log all messages
			t.Logf("Messages received:")
			for j, msg := range messages {
				t.Logf("  [%d] %s", j, msg)
			}

			// Verify order
			expectedOrder := []string{
				`STDOUT: "hello\n"`,
				"EXIT: 0",
				"CLOSE",
			}

			if len(messages) != len(expectedOrder) {
				t.Errorf("Expected %d messages, got %d", len(expectedOrder), len(messages))
			}

			for j := 0; j < len(expectedOrder) && j < len(messages); j++ {
				if messages[j] != expectedOrder[j] {
					t.Errorf("Message %d mismatch: expected %q, got %q", j, expectedOrder[j], messages[j])
				}
			}
		})
	}
}

// TestWebSocketWithDelay tests if adding a small delay fixes the race condition
func TestWebSocketWithDelay(t *testing.T) {
	// Run the test with 20 concurrent clients (where we see the most failures)
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		// Create a new session for each request
		session := NewSession(
			WithCommand("echo", "hello"),
			WithTTY(false),
		)
		handler := NewWebSocketHandler(session)
		if err := handler.Handle(w, r); err != nil {
			t.Errorf("handler error: %v", err)
		}
	}))
	defer server.Close()

	var wg sync.WaitGroup
	results := make(chan string, 20)

	// Launch 20 concurrent clients
	for i := 0; i < 20; i++ {
		wg.Add(1)
		go func(clientID int) {
			defer wg.Done()

			// Connect as WebSocket client
			wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
			dialer := gorillaws.DefaultDialer
			conn, _, err := dialer.Dial(wsURL, nil)
			if err != nil {
				results <- fmt.Sprintf("client %d: connection failed: %v", clientID, err)
				return
			}
			defer conn.Close()

			// Track message order
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
							messages = append(messages, "stdout")
						case StreamExit:
							messages = append(messages, "exit")
							// Add a small delay here to allow any in-flight messages to arrive
							time.Sleep(10 * time.Millisecond)
							return
						}
					}
				}
			}()

			// Wait for completion
			select {
			case <-done:
			case <-time.After(2 * time.Second):
				results <- fmt.Sprintf("client %d: timeout", clientID)
				return
			}

			// Check message order
			if len(messages) == 2 && messages[0] == "stdout" && messages[1] == "exit" {
				results <- fmt.Sprintf("client %d: correct order", clientID)
			} else if len(messages) == 2 && messages[0] == "exit" && messages[1] == "stdout" {
				results <- fmt.Sprintf("client %d: WRONG ORDER (exit before stdout)", clientID)
			} else if len(messages) == 1 && messages[0] == "exit" {
				results <- fmt.Sprintf("client %d: NO STDOUT received", clientID)
			} else {
				results <- fmt.Sprintf("client %d: unexpected messages: %v", clientID, messages)
			}
		}(i)
	}

	// Wait for all clients to complete
	wg.Wait()
	close(results)

	// Analyze results
	correctCount := 0
	wrongCount := 0

	for result := range results {
		t.Logf("  %s", result)
		if strings.Contains(result, "correct order") {
			correctCount++
		} else {
			wrongCount++
		}
	}

	t.Logf("Summary: %d correct, %d wrong out of 20 clients", correctCount, wrongCount)
	if wrongCount > 0 {
		t.Logf("With 10ms delay: %.1f%% failure rate", float64(wrongCount)*100/20)
		// Don't fail the test - we're just checking if delay helps
	}
}

// TestWebSocketUnderCPULoad tests sequential clients while CPU is under heavy load
func TestWebSocketUnderCPULoad(t *testing.T) {
	// Start CPU-intensive goroutines to consume available CPU
	numCPU := runtime.NumCPU()
	stopCPU := make(chan struct{})

	// Start CPU burners (one less than total CPUs to leave some headroom)
	for i := 0; i < numCPU-1; i++ {
		go func() {
			// Busy loop to consume CPU
			x := 0
			for {
				select {
				case <-stopCPU:
					return
				default:
					// CPU-intensive work
					x = (x + 1) % 1000000
					_ = x * x * x
				}
			}
		}()
	}
	defer close(stopCPU)

	// Give CPU burners time to start
	time.Sleep(100 * time.Millisecond)

	// Now run sequential clients
	numClients := 20
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		// Create a new session for each request
		session := NewSession(
			WithCommand("echo", "hello"),
			WithTTY(false),
		)
		handler := NewWebSocketHandler(session)
		if err := handler.Handle(w, r); err != nil {
			t.Errorf("handler error: %v", err)
		}
	}))
	defer server.Close()

	results := []string{}

	// Launch clients SEQUENTIALLY while CPU is loaded
	for i := 0; i < numClients; i++ {
		// Connect as WebSocket client
		wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
		dialer := gorillaws.DefaultDialer
		conn, _, err := dialer.Dial(wsURL, nil)
		if err != nil {
			results = append(results, fmt.Sprintf("client %d: connection failed: %v", i, err))
			continue
		}

		// Track message order
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
						messages = append(messages, "stdout")
					case StreamExit:
						messages = append(messages, "exit")
						return
					}
				}
			}
		}()

		// Wait for completion
		select {
		case <-done:
		case <-time.After(2 * time.Second):
			results = append(results, fmt.Sprintf("client %d: timeout", i))
			conn.Close()
			continue
		}

		// Check message order
		if len(messages) == 2 && messages[0] == "stdout" && messages[1] == "exit" {
			results = append(results, fmt.Sprintf("client %d: correct order", i))
		} else if len(messages) == 2 && messages[0] == "exit" && messages[1] == "stdout" {
			results = append(results, fmt.Sprintf("client %d: WRONG ORDER (exit before stdout)", i))
		} else if len(messages) == 1 && messages[0] == "exit" {
			results = append(results, fmt.Sprintf("client %d: NO STDOUT received", i))
		} else {
			results = append(results, fmt.Sprintf("client %d: unexpected messages: %v", i, messages))
		}

		conn.Close()
	}

	// Analyze results
	correctCount := 0
	wrongCount := 0

	for _, result := range results {
		t.Logf("  %s", result)
		if strings.Contains(result, "correct order") {
			correctCount++
		} else {
			wrongCount++
		}
	}

	t.Logf("Summary: %d correct, %d wrong out of %d clients (under CPU load)", correctCount, wrongCount, numClients)
	if wrongCount > 0 {
		t.Errorf("RACE CONDITION DETECTED under CPU load: %.1f%% failure rate",
			float64(wrongCount)*100/float64(numClients))
	}
}

// TestWebSocketDebugTiming tests with detailed logging to understand the timing
func TestWebSocketDebugTiming(t *testing.T) {
	// Start with high CPU load
	numCPU := runtime.NumCPU()
	stopCPU := make(chan struct{})

	// Start CPU burners
	for i := 0; i < numCPU-1; i++ {
		go func() {
			x := 0
			for {
				select {
				case <-stopCPU:
					return
				default:
					x = (x + 1) % 1000000
					_ = x * x * x
				}
			}
		}()
	}
	defer close(stopCPU)

	// Give CPU burners time to start
	time.Sleep(100 * time.Millisecond)

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		// Use a command that produces more output to increase chance of preemption
		session := NewSession(
			WithCommand("sh", "-c", "echo START; echo MIDDLE; echo END"),
			WithTTY(false),
		)
		handler := NewWebSocketHandler(session)
		if err := handler.Handle(w, r); err != nil {
			t.Errorf("handler error: %v", err)
		}
	}))
	defer server.Close()

	// Test just one client
	wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
	dialer := gorillaws.DefaultDialer
	conn, _, err := dialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("connection failed: %v", err)
	}
	defer conn.Close()

	// Track all messages with timestamps
	type messageInfo struct {
		stream string
		data   string
		time   time.Time
	}
	var messages []messageInfo
	done := make(chan struct{})

	startTime := time.Now()
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
					messages = append(messages, messageInfo{
						stream: "stdout",
						data:   string(data[1:]),
						time:   time.Now(),
					})
				case StreamExit:
					exitCode := int(data[1])
					messages = append(messages, messageInfo{
						stream: "exit",
						data:   fmt.Sprintf("code=%d", exitCode),
						time:   time.Now(),
					})
					return
				}
			}
		}
	}()

	// Wait for completion
	select {
	case <-done:
	case <-time.After(5 * time.Second):
		t.Fatal("timeout waiting for exit")
	}

	// Print detailed timing info
	t.Logf("Message sequence (CPU load active):")
	gotStdout := false
	for i, msg := range messages {
		elapsed := msg.time.Sub(startTime)
		t.Logf("  [%d] %v: %s = %s", i, elapsed, msg.stream, msg.data)
		if msg.stream == "stdout" {
			gotStdout = true
		}
	}

	if !gotStdout {
		t.Errorf("NO STDOUT RECEIVED under CPU load")
	} else if len(messages) > 0 && messages[len(messages)-1].stream != "exit" {
		t.Errorf("Last message was not exit code")
	}
}

// TestWebSocketDetailedDebug tests with extreme logging to understand the issue
func TestWebSocketDetailedDebug(t *testing.T) {
	// Start with high CPU load
	numCPU := runtime.NumCPU()
	stopCPU := make(chan struct{})

	// Start CPU burners
	for i := 0; i < numCPU-1; i++ {
		go func() {
			x := 0
			for {
				select {
				case <-stopCPU:
					return
				default:
					x = (x + 1) % 1000000
					_ = x * x * x
				}
			}
		}()
	}
	defer close(stopCPU)

	// Give CPU burners time to start
	time.Sleep(100 * time.Millisecond)

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		// Create a session with debugging
		session := NewSession(
			WithCommand("sh", "-c", "echo 'TEST OUTPUT'; exit 0"),
			WithTTY(false),
		)

		// Add logging to session callbacks
		originalCallback := session.onProcessStart
		session.onProcessStart = func(pid int) {
			t.Logf("[SERVER] Process started with PID %d", pid)
			if originalCallback != nil {
				originalCallback(pid)
			}
		}

		handler := NewWebSocketHandler(session)
		t.Logf("[SERVER] Starting WebSocket handler")
		if err := handler.Handle(w, r); err != nil {
			t.Errorf("handler error: %v", err)
		}
		t.Logf("[SERVER] WebSocket handler completed")
	}))
	defer server.Close()

	// Test just one client
	wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
	dialer := gorillaws.DefaultDialer
	conn, _, err := dialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("connection failed: %v", err)
	}
	defer conn.Close()

	// Track all messages
	var messages []string
	done := make(chan struct{})

	go func() {
		defer close(done)
		for {
			messageType, data, err := conn.ReadMessage()
			if err != nil {
				t.Logf("[CLIENT] Read error: %v", err)
				return
			}

			if messageType == gorillaws.BinaryMessage && len(data) > 0 {
				stream := StreamID(data[0])
				switch stream {
				case StreamStdout:
					output := string(data[1:])
					t.Logf("[CLIENT] Received stdout: %q", output)
					messages = append(messages, fmt.Sprintf("stdout:%q", output))
				case StreamExit:
					exitCode := int(data[1])
					t.Logf("[CLIENT] Received exit code: %d", exitCode)
					messages = append(messages, fmt.Sprintf("exit:%d", exitCode))
					return
				default:
					t.Logf("[CLIENT] Received unknown stream %d", stream)
				}
			}
		}
	}()

	// Wait for completion
	select {
	case <-done:
		t.Logf("[CLIENT] Connection closed")
	case <-time.After(5 * time.Second):
		t.Fatal("timeout waiting for exit")
	}

	// Analyze results
	t.Logf("Final message sequence: %v", messages)

	hasStdout := false
	hasExit := false
	for _, msg := range messages {
		if strings.HasPrefix(msg, "stdout:") {
			hasStdout = true
		}
		if strings.HasPrefix(msg, "exit:") {
			hasExit = true
		}
	}

	if !hasStdout {
		t.Errorf("NO STDOUT RECEIVED! Messages: %v", messages)
	}
	if !hasExit {
		t.Errorf("NO EXIT CODE RECEIVED! Messages: %v", messages)
	}
}

// TestWebSocketTTYUnderCPULoad tests TTY mode under high CPU load
func TestWebSocketTTYUnderCPULoad(t *testing.T) {
	if runtime.GOOS == "windows" {
		t.Skip("PTY not supported on Windows")
	}

	// Start CPU-intensive goroutines to consume available CPU
	numCPU := runtime.NumCPU()
	stopCPU := make(chan struct{})

	// Start CPU burners (one less than total CPUs to leave some headroom)
	for i := 0; i < numCPU-1; i++ {
		go func() {
			// Busy loop to consume CPU
			x := 0
			for {
				select {
				case <-stopCPU:
					return
				default:
					// CPU-intensive work
					x = (x + 1) % 1000000
					_ = x * x * x
				}
			}
		}()
	}
	defer close(stopCPU)

	// Give CPU burners time to start
	time.Sleep(100 * time.Millisecond)

	// Now run sequential clients with TTY
	numClients := 20
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		// Create a new session for each request
		session := NewSession(
			WithCommand("echo", "hello"),
			WithTTY(true), // Enable TTY mode
		)
		handler := NewWebSocketHandler(session)
		if err := handler.Handle(w, r); err != nil {
			t.Errorf("handler error: %v", err)
		}
	}))
	defer server.Close()

	correctCount := 0
	noOutputCount := 0

	// Launch clients SEQUENTIALLY while CPU is loaded
	for i := 0; i < numClients; i++ {
		// Connect as WebSocket client
		wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
		dialer := gorillaws.DefaultDialer
		conn, _, err := dialer.Dial(wsURL, nil)
		if err != nil {
			t.Errorf("client %d: connection failed: %v", i, err)
			continue
		}

		// Track received data
		receivedOutput := false
		receivedExit := false
		done := make(chan struct{})

		go func() {
			defer close(done)
			for {
				messageType, data, err := conn.ReadMessage()
				if err != nil {
					return
				}

				if messageType == gorillaws.TextMessage {
					// TTY mode uses text messages
					if strings.Contains(string(data), "hello") {
						receivedOutput = true
					}
				} else if messageType == gorillaws.BinaryMessage && len(data) > 0 {
					stream := StreamID(data[0])
					if stream == StreamExit {
						receivedExit = true
						return
					}
				}
			}
		}()

		// Wait for completion
		select {
		case <-done:
		case <-time.After(2 * time.Second):
			t.Logf("client %d: timeout", i)
			conn.Close()
			continue
		}

		// Check results
		if receivedOutput && receivedExit {
			correctCount++
			t.Logf("client %d: correct (received output and exit)", i)
		} else if !receivedOutput && receivedExit {
			noOutputCount++
			t.Logf("client %d: NO OUTPUT received (only exit)", i)
		} else {
			t.Logf("client %d: unexpected state (output=%v, exit=%v)", i, receivedOutput, receivedExit)
		}

		conn.Close()
	}

	t.Logf("TTY Summary: %d correct, %d no output, %d total", correctCount, noOutputCount, numClients)
	if noOutputCount > 0 {
		t.Errorf("RACE CONDITION in TTY mode: %d clients received no output", noOutputCount)
	}
}

// TestWebSocketUnderCPULoadAlternative shows a cleaner way to test under constrained resources
func TestWebSocketUnderCPULoadAlternative(t *testing.T) {
	// Save original GOMAXPROCS
	originalGOMAXPROCS := runtime.GOMAXPROCS(0)
	defer runtime.GOMAXPROCS(originalGOMAXPROCS)

	// Limit to 1 CPU - this forces all goroutines to compete for a single processor
	runtime.GOMAXPROCS(1)

	// Now run test with many concurrent operations
	// They'll all compete for the single available processor
	numClients := 20
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		session := NewSession(
			WithCommand("echo", "hello"),
			WithTTY(false),
		)
		handler := NewWebSocketHandler(session)
		if err := handler.Handle(w, r); err != nil {
			t.Errorf("handler error: %v", err)
		}
	}))
	defer server.Close()

	// Launch many goroutines that will compete for CPU time
	var wg sync.WaitGroup
	results := make([]string, numClients)

	for i := 0; i < numClients; i++ {
		wg.Add(1)
		go func(idx int) {
			defer wg.Done()

			// Each client runs in its own goroutine
			wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
			dialer := gorillaws.DefaultDialer
			conn, _, err := dialer.Dial(wsURL, nil)
			if err != nil {
				results[idx] = fmt.Sprintf("client %d: connection failed: %v", idx, err)
				return
			}
			defer conn.Close()

			// Track message order
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
							messages = append(messages, "stdout")
						case StreamExit:
							messages = append(messages, "exit")
							return
						}
					}
				}
			}()

			// Wait for completion
			select {
			case <-done:
			case <-time.After(2 * time.Second):
				results[idx] = fmt.Sprintf("client %d: timeout", idx)
				return
			}

			// Check message order
			if len(messages) == 2 && messages[0] == "stdout" && messages[1] == "exit" {
				results[idx] = fmt.Sprintf("client %d: correct order", idx)
			} else if len(messages) == 2 && messages[0] == "exit" && messages[1] == "stdout" {
				results[idx] = fmt.Sprintf("client %d: WRONG ORDER (exit before stdout)", idx)
			} else if len(messages) == 1 && messages[0] == "exit" {
				results[idx] = fmt.Sprintf("client %d: NO STDOUT received", idx)
			} else {
				results[idx] = fmt.Sprintf("client %d: unexpected messages: %v", idx, messages)
			}
		}(i)
	}

	wg.Wait()

	// Analyze results
	correctCount := 0
	wrongCount := 0

	for _, result := range results {
		t.Logf("  %s", result)
		if strings.Contains(result, "correct order") {
			correctCount++
		} else {
			wrongCount++
		}
	}

	t.Logf("Summary: %d correct, %d wrong out of %d clients (GOMAXPROCS=1)", correctCount, wrongCount, numClients)
	if wrongCount > 0 {
		t.Errorf("Race condition detected with GOMAXPROCS=1: %.1f%% failure rate",
			float64(wrongCount)*100/float64(numClients))
	}
}

// TestWebSocketNoReadyMessage verifies that StreamReady is no longer sent
func TestWebSocketNoReadyMessage(t *testing.T) {
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		session := NewSession(
			WithCommand("echo", "hello"),
			WithTTY(false),
		)
		handler := NewWebSocketHandler(session)
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

	// Read first message
	messageType, data, err := conn.ReadMessage()
	if err != nil {
		t.Fatalf("failed to read first message: %v", err)
	}

	// Verify the first message is stdout, not StreamReady
	if messageType != gorillaws.BinaryMessage {
		t.Errorf("expected binary message, got type %d", messageType)
	}

	// First message should be stdout with "hello\n"
	if len(data) < 2 || StreamID(data[0]) != StreamStdout {
		t.Errorf("expected first message to be StreamStdout (0x01) with content, got %#v", data)
	}
	if len(data) > 0 && StreamID(data[0]) == StreamReady {
		t.Errorf("StreamReady message should not be sent anymore")
	}

	t.Log("✓ No StreamReady message sent, first message is stdout as expected")
}
