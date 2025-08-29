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

// TestWebSocketStderrIntegration tests various real-world scenarios
func TestWebSocketStderrIntegration(t *testing.T) {
	testCases := []struct {
		name           string
		command        []string
		expectStdout   []string
		expectStderr   []string
		expectExitCode int
	}{
		{
			name:           "python script with stderr warning",
			command:        []string{"sh", "-c", "echo 'Result: 42'; echo 'Warning: deprecated function' >&2"},
			expectStdout:   []string{"Result: 42"},
			expectStderr:   []string{"Warning: deprecated function"},
			expectExitCode: 0,
		},
		{
			name:           "npm command with stderr output",
			command:        []string{"sh", "-c", "echo 'npm WARN deprecated package@1.0.0' >&2; echo 'added 5 packages'"},
			expectStdout:   []string{"added 5 packages"},
			expectStderr:   []string{"npm WARN deprecated package@1.0.0"},
			expectExitCode: 0,
		},
		{
			name:           "curl with progress to stderr",
			command:        []string{"sh", "-c", "echo 'Progress: 50%' >&2; echo 'Progress: 100%' >&2; echo 'Download complete'"},
			expectStdout:   []string{"Download complete"},
			expectStderr:   []string{"Progress: 50%", "Progress: 100%"},
			expectExitCode: 0,
		},
		{
			name:           "compiler error output",
			command:        []string{"sh", "-c", "echo 'main.c:10: error: undefined reference' >&2; exit 1"},
			expectStdout:   []string{},
			expectStderr:   []string{"main.c:10: error: undefined reference"},
			expectExitCode: 1,
		},
		{
			name:           "mixed output with timing",
			command:        []string{"sh", "-c", "echo out1; sleep 0.01; echo err1 >&2; sleep 0.01; echo out2; sleep 0.01; echo err2 >&2"},
			expectStdout:   []string{"out1", "out2"},
			expectStderr:   []string{"err1", "err2"},
			expectExitCode: 0,
		},
		{
			name:           "empty stdout with stderr only",
			command:        []string{"sh", "-c", "echo 'ERROR: File not found' >&2; echo 'ERROR: Permission denied' >&2; exit 1"},
			expectStdout:   []string{},
			expectStderr:   []string{"ERROR: File not found", "ERROR: Permission denied"},
			expectExitCode: 1,
		},
		{
			name:           "large stderr output with small stdout",
			command:        []string{"sh", "-c", "echo 'Starting...'; for i in $(seq 1 50); do echo \"DEBUG: Processing item $i\" >&2; done; echo 'Done'"},
			expectStdout:   []string{"Starting...", "Done"},
			expectStderr:   []string{"DEBUG: Processing item 1", "DEBUG: Processing item 50"}, // Check first and last
			expectExitCode: 0,
		},
		{
			name:           "stderr with special characters",
			command:        []string{"sh", "-c", "echo 'Error: Failed to parse JSON: {\"key\": \"value\"}' >&2"},
			expectStdout:   []string{},
			expectStderr:   []string{`Error: Failed to parse JSON: {"key": "value"}`},
			expectExitCode: 0,
		},
		{
			name:           "stderr with ANSI color codes",
			command:        []string{"sh", "-c", "echo -e '\\033[31mERROR\\033[0m: Something went wrong' >&2"},
			expectStdout:   []string{},
			expectStderr:   []string{"\033[31mERROR\033[0m: Something went wrong"},
			expectExitCode: 0,
		},
		{
			name:           "rapid alternating output",
			command:        []string{"sh", "-c", "for i in 1 2 3 4 5; do echo \"out$i\"; echo \"err$i\" >&2; done"},
			expectStdout:   []string{"out1", "out2", "out3", "out4", "out5"},
			expectStderr:   []string{"err1", "err2", "err3", "err4", "err5"},
			expectExitCode: 0,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
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

			wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
			dialer := gorillaws.DefaultDialer
			conn, _, err := dialer.Dial(wsURL, nil)
			if err != nil {
				t.Fatalf("failed to connect: %v", err)
			}
			defer conn.Close()

			var mu sync.Mutex
			stdoutLines := []string{}
			stderrLines := []string{}
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
							text := string(payload)
							for _, line := range strings.Split(strings.TrimSpace(text), "\n") {
								if line != "" {
									stdoutLines = append(stdoutLines, line)
								}
							}
						case StreamStderr:
							text := string(payload)
							for _, line := range strings.Split(strings.TrimSpace(text), "\n") {
								if line != "" {
									stderrLines = append(stderrLines, line)
								}
							}
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

			select {
			case <-done:
			case <-time.After(5 * time.Second):
				t.Fatal("test timeout")
			}

			mu.Lock()
			defer mu.Unlock()

			if !exitCodeReceived {
				t.Error("exit code not received")
			} else if exitCode != tc.expectExitCode {
				t.Errorf("exit code mismatch: expected %d, got %d", tc.expectExitCode, exitCode)
			}

			// Check stdout
			for _, expected := range tc.expectStdout {
				found := false
				for _, line := range stdoutLines {
					if strings.Contains(line, expected) {
						found = true
						break
					}
				}
				if !found {
					t.Errorf("stdout missing expected content %q, got: %v", expected, stdoutLines)
				}
			}

			// Check stderr
			for _, expected := range tc.expectStderr {
				found := false
				for _, line := range stderrLines {
					if strings.Contains(line, expected) {
						found = true
						break
					}
				}
				if !found {
					t.Errorf("stderr missing expected content %q, got: %v", expected, stderrLines)
				}
			}

			// Log summary
			t.Logf("Captured stdout lines: %d, stderr lines: %d", len(stdoutLines), len(stderrLines))
		})
	}
}

// TestWebSocketStderrConcurrency tests concurrent writes to stdout and stderr
func TestWebSocketStderrConcurrency(t *testing.T) {
	// Command that writes concurrently to both streams
	script := `
#!/bin/bash
for i in $(seq 1 20); do
    echo "stdout line $i" &
    echo "stderr line $i" >&2 &
done
wait
`
	session := NewSession(
		WithCommand("bash", "-c", script),
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

	var mu sync.Mutex
	stdoutCount := 0
	stderrCount := 0
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
					for _, line := range strings.Split(string(payload), "\n") {
						if strings.Contains(line, "stdout line") {
							stdoutCount++
						}
					}
				case StreamStderr:
					for _, line := range strings.Split(string(payload), "\n") {
						if strings.Contains(line, "stderr line") {
							stderrCount++
						}
					}
				case StreamExit:
					mu.Unlock()
					return
				}
				mu.Unlock()
			}
		}
	}()

	select {
	case <-done:
	case <-time.After(5 * time.Second):
		t.Fatal("test timeout")
	}

	mu.Lock()
	defer mu.Unlock()

	// We should have received 20 lines on each stream
	if stdoutCount != 20 {
		t.Errorf("expected 20 stdout lines, got %d", stdoutCount)
	}
	if stderrCount != 20 {
		t.Errorf("expected 20 stderr lines, got %d", stderrCount)
	}
}

// TestWebSocketStderrBuffer tests that buffered stderr is properly handled
func TestWebSocketStderrBuffer(t *testing.T) {
	// Command that writes without newlines to test buffering
	session := NewSession(
		WithCommand("sh", "-c", "printf 'stdout no newline'; printf 'stderr no newline' >&2"),
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

	var mu sync.Mutex
	stdoutReceived := ""
	stderrReceived := ""
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
					stdoutReceived += string(payload)
				case StreamStderr:
					stderrReceived += string(payload)
				case StreamExit:
					mu.Unlock()
					return
				}
				mu.Unlock()
			}
		}
	}()

	select {
	case <-done:
	case <-time.After(2 * time.Second):
		t.Fatal("test timeout")
	}

	mu.Lock()
	defer mu.Unlock()

	if stdoutReceived != "stdout no newline" {
		t.Errorf("stdout mismatch: expected %q, got %q", "stdout no newline", stdoutReceived)
	}
	if stderrReceived != "stderr no newline" {
		t.Errorf("stderr mismatch: expected %q, got %q", "stderr no newline", stderrReceived)
	}
}

// TestWebSocketStderrPerformance tests performance with high-volume stderr output
func TestWebSocketStderrPerformance(t *testing.T) {
	// Command that generates a lot of stderr output quickly
	session := NewSession(
		WithCommand("sh", "-c", "for i in $(seq 1 1000); do echo \"Error $i: This is a detailed error message with some context\" >&2; done"),
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

	startTime := time.Now()
	var mu sync.Mutex
	stderrLineCount := 0
	totalStderrBytes := 0
	stderrBuffer := "" // Buffer for incomplete lines
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
				case StreamStderr:
					totalStderrBytes += len(payload)
					// Append to buffer to handle lines split across messages
					stderrBuffer += string(payload)
					// Process complete lines
					lines := strings.Split(stderrBuffer, "\n")
					// Keep the last element as it might be incomplete
					if len(lines) > 1 {
						// Process all complete lines
						for i := 0; i < len(lines)-1; i++ {
							if strings.Contains(lines[i], "Error") {
								stderrLineCount++
							}
						}
						// Keep the incomplete line in buffer
						stderrBuffer = lines[len(lines)-1]
					}
				case StreamExit:
					mu.Unlock()
					return
				}
				mu.Unlock()
			}
		}
	}()

	select {
	case <-done:
	case <-time.After(10 * time.Second):
		t.Fatal("test timeout - performance issue?")
	}

	duration := time.Since(startTime)

	mu.Lock()
	defer mu.Unlock()

	// Check any remaining data in buffer
	if stderrBuffer != "" && strings.Contains(stderrBuffer, "Error") {
		stderrLineCount++
	}

	if stderrLineCount != 1000 {
		t.Errorf("expected 1000 stderr lines, got %d", stderrLineCount)
	}

	throughput := float64(totalStderrBytes) / duration.Seconds() / 1024 / 1024 // MB/s
	t.Logf("Performance: processed %d stderr lines (%d bytes) in %v (%.2f MB/s)",
		stderrLineCount, totalStderrBytes, duration, throughput)
}
