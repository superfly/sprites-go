package terminal

import (
	"bytes"
	"fmt"
	"io"
	"net/http"
	"net/http/httptest"
	"os"
	"strings"
	"testing"
	"time"

	expect "github.com/Netflix/go-expect"
	gorillaws "github.com/gorilla/websocket"
)

// TestControlSequencePreservation verifies that all control sequences are passed through exactly as-is
func TestControlSequencePreservation(t *testing.T) {
	// This test always runs in Linux Docker environment

	tests := []struct {
		name           string
		command        []string
		input          string
		expectedOutput []string // Multiple strings to check in order
		description    string
	}{
		{
			name:    "AlternateScreenBuffer",
			command: []string{"sh", "-c", "printf '\\033[?1049h'; sleep 0.1; printf 'Hello from alternate screen'; sleep 0.1; printf '\\033[?1049l'"},
			expectedOutput: []string{
				"\x1b[?1049h",                 // Enter alternate screen
				"Hello from alternate screen", // Content
				"\x1b[?1049l",                 // Exit alternate screen
			},
			description: "Tests alternate screen buffer sequences (smcup/rmcup) used by vim, top, htop",
		},
		{
			name:    "CursorMovementSequences",
			command: []string{"sh", "-c", "printf '\\033[H'; printf '\\033[2J'; printf '\\033[10;20H'; printf 'Cursor at 10,20'"},
			expectedOutput: []string{
				"\x1b[H",          // Cursor home
				"\x1b[2J",         // Clear screen
				"\x1b[10;20H",     // Move cursor to row 10, col 20
				"Cursor at 10,20", // Text at position
			},
			description: "Tests cursor movement control sequences",
		},
		{
			name:    "ColorSequences",
			command: []string{"sh", "-c", "printf '\\033[31mRed\\033[0m \\033[32mGreen\\033[0m \\033[34mBlue\\033[0m'"},
			expectedOutput: []string{
				"\x1b[31m", // Red color
				"Red",
				"\x1b[0m",  // Reset
				"\x1b[32m", // Green color
				"Green",
				"\x1b[0m",  // Reset
				"\x1b[34m", // Blue color
				"Blue",
				"\x1b[0m", // Reset
			},
			description: "Tests ANSI color escape sequences",
		},
		{
			name:    "ComplexSequences",
			command: []string{"sh", "-c", "printf '\\033[1m\\033[4m\\033[31mBold Underline Red\\033[0m\\n\\033[?25l\\033[?25h'"},
			expectedOutput: []string{
				"\x1b[1m",            // Bold
				"\x1b[4m",            // Underline
				"\x1b[31m",           // Red
				"Bold Underline Red", // Text
				"\x1b[0m",            // Reset all
				"\x1b[?25l",          // Hide cursor
				"\x1b[?25h",          // Show cursor
			},
			description: "Tests complex combination of escape sequences",
		},
		{
			name:    "SaveRestoreCursor",
			command: []string{"sh", "-c", "printf '\\0337'; printf 'First line\\n'; printf '\\0338'; printf 'Overwrite'"},
			expectedOutput: []string{
				"\x1b7",      // Save cursor position
				"First line", // Text
				"\n",         // Newline
				"\x1b8",      // Restore cursor position
				"Overwrite",  // Overwrite at saved position
			},
			description: "Tests save/restore cursor position sequences",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Create a session with PTY enabled
			session := NewSession(
				WithCommand(tt.command[0], tt.command[1:]...),
				WithTTY(true),
				WithTerminalSize(80, 24),
			)

			// Create WebSocket handler
			handler := NewWebSocketHandler(session)

			// Start test server
			server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
				err := handler.Handle(w, r)
				if err != nil {
					t.Logf("Handler error: %v", err)
				}
			}))
			defer server.Close()

			// Connect WebSocket client
			wsURL := strings.Replace(server.URL, "http://", "ws://", 1)
			dialer := gorillaws.DefaultDialer
			dialer.ReadBufferSize = 1024 * 1024
			dialer.WriteBufferSize = 1024 * 1024

			conn, _, err := dialer.Dial(wsURL, nil)
			if err != nil {
				t.Fatalf("Failed to connect WebSocket: %v", err)
			}
			defer conn.Close()

			// Collect all output
			output := &bytes.Buffer{}
			done := make(chan error, 1)

			go func() {
				for {
					messageType, data, err := conn.ReadMessage()
					if err != nil {
						done <- err
						return
					}
					if messageType == gorillaws.BinaryMessage {
						output.Write(data)
					}
				}
			}()

			// Send input if provided
			if tt.input != "" {
				time.Sleep(100 * time.Millisecond) // Let command start
				err = conn.WriteMessage(gorillaws.BinaryMessage, []byte(tt.input))
				if err != nil {
					t.Fatalf("Failed to send input: %v", err)
				}
			}

			// Wait for output or timeout
			select {
			case <-done:
				// Connection closed
			case <-time.After(2 * time.Second):
				// Timeout - close connection
				conn.Close()
				<-done
			}

			// Check that all expected sequences are present in order
			outputStr := output.String()
			t.Logf("%s output (hex): %x", tt.name, outputStr)
			t.Logf("%s output (string): %q", tt.name, outputStr)

			lastIndex := 0
			for _, expected := range tt.expectedOutput {
				index := strings.Index(outputStr[lastIndex:], expected)
				if index == -1 {
					t.Errorf("%s: Expected sequence %q not found in output", tt.description, expected)
					t.Logf("Full output: %q", outputStr)
					break
				}
				lastIndex += index + len(expected)
			}
		})
	}
}

// TestRawByteOrdering verifies that bytes are received in order without buffering
func TestRawByteOrdering(t *testing.T) {
	// This test always runs in Linux Docker environment

	// Generate a large amount of sequential data to test for buffering issues
	var testData bytes.Buffer
	for i := 0; i < 1000; i++ {
		fmt.Fprintf(&testData, "Line %04d: The quick brown fox jumps over the lazy dog. ", i)
		// Add some control sequences in between
		if i%100 == 0 {
			testData.WriteString("\x1b[31m[MARKER]\x1b[0m ")
		}
		testData.WriteString("\n")
	}

	// Create a script that outputs data without buffering
	script := fmt.Sprintf("printf '%s'", strings.ReplaceAll(testData.String(), "'", "'\"'\"'"))

	session := NewSession(
		WithCommand("sh", "-c", script),
		WithTTY(true),
		WithTerminalSize(120, 40),
	)

	handler := NewWebSocketHandler(session)
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		err := handler.Handle(w, r)
		if err != nil {
			t.Logf("Handler error: %v", err)
		}
	}))
	defer server.Close()

	wsURL := strings.Replace(server.URL, "http://", "ws://", 1)
	dialer := gorillaws.DefaultDialer
	dialer.ReadBufferSize = 1024 * 1024
	dialer.WriteBufferSize = 1024 * 1024

	conn, _, err := dialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("Failed to connect WebSocket: %v", err)
	}
	defer conn.Close()

	// Collect output and verify ordering
	var received bytes.Buffer
	messageCount := 0
	done := make(chan error, 1)

	go func() {
		for {
			messageType, data, err := conn.ReadMessage()
			if err != nil {
				done <- err
				return
			}
			if messageType == gorillaws.BinaryMessage {
				received.Write(data)
				messageCount++
			}
		}
	}()

	// Wait for completion
	select {
	case <-done:
		// Connection closed
	case <-time.After(3 * time.Second):
		conn.Close()
		<-done
	}

	receivedStr := received.String()
	t.Logf("Received %d messages, total %d bytes", messageCount, len(receivedStr))

	// Verify all lines are in order
	lines := strings.Split(receivedStr, "\n")
	lastLineNum := -1
	for _, line := range lines {
		if strings.HasPrefix(line, "Line ") && len(line) > 9 {
			var lineNum int
			_, err := fmt.Sscanf(line[:9], "Line %d", &lineNum)
			if err == nil {
				if lineNum <= lastLineNum {
					t.Errorf("Lines out of order: line %d came after line %d", lineNum, lastLineNum)
				}
				lastLineNum = lineNum
			}
		}
	}

	// Verify markers are present and properly formatted
	markerCount := strings.Count(receivedStr, "\x1b[31m[MARKER]\x1b[0m")
	expectedMarkers := 10 // One every 100 lines for 1000 lines
	if markerCount != expectedMarkers {
		t.Errorf("Expected %d markers, found %d", expectedMarkers, markerCount)
	}
}

// TestInteractivePTYWithExpect uses go-expect to test interactive PTY behavior
func TestInteractivePTYWithExpect(t *testing.T) {
	// This test always runs in Linux Docker environment

	// Create a simple interactive shell session
	session := NewSession(
		WithCommand("sh"),
		WithTTY(true),
		WithTerminalSize(80, 24),
	)

	handler := NewWebSocketHandler(session)
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		err := handler.Handle(w, r)
		if err != nil {
			t.Logf("Handler error: %v", err)
		}
	}))
	defer server.Close()

	// Create expect console
	console, err := expect.NewConsole(expect.WithStdout(os.Stdout))
	if err != nil {
		t.Fatalf("Failed to create expect console: %v", err)
	}
	defer console.Close()

	// Connect WebSocket
	wsURL := strings.Replace(server.URL, "http://", "ws://", 1)
	dialer := gorillaws.DefaultDialer
	conn, _, err := dialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("Failed to connect WebSocket: %v", err)
	}
	defer conn.Close()

	// Create adapter for bidirectional communication
	adapter := NewAdapter(conn, true)
	defer adapter.Close()

	// Connect console to WebSocket adapter
	go io.Copy(adapter, console.Tty())
	go io.Copy(console.Tty(), adapter)

	// Test interactive commands with expect
	t.Run("EchoCommand", func(t *testing.T) {
		console.SendLine("echo 'Hello from expect'")
		out, err := console.ExpectString("Hello from expect")
		if err != nil {
			t.Errorf("Failed to find expected output: %v", err)
		}
		t.Logf("Got output: %s", out)
	})

	t.Run("ControlSequenceInPrompt", func(t *testing.T) {
		// Test PS1 with color codes - use printf to set the prompt with proper escaping
		console.SendLine("PS1=$(printf '\\033[32m$\\033[0m ')")
		time.Sleep(100 * time.Millisecond)

		// Send another command to see the colored prompt
		console.SendLine("echo test")
		// Use a more specific pattern that captures the full output including prompt
		out, err := console.Expect(expect.RegexpPattern(`.*test.*`))
		if err != nil {
			t.Errorf("Failed to find test output: %v", err)
		}

		// Check that we got the green prompt
		if !strings.Contains(out, "\x1b[32m") {
			t.Errorf("Expected green color code in prompt, got: %q", out)
		}
	})

	// Exit shell
	console.SendLine("exit")
}

// TestFullScreenAppSimulation simulates a full-screen terminal app
func TestFullScreenAppSimulation(t *testing.T) {
	// This test always runs in Linux Docker environment

	// Script that simulates a full-screen app like vim or top
	fullScreenScript := `#!/bin/sh
# Enter alternate screen
printf '\033[?1049h'
# Clear screen
printf '\033[2J'
# Move to top
printf '\033[H'
# Draw a border
printf '+----------------------------------------+\n'
printf '|         Full Screen App Test           |\n'
printf '+----------------------------------------+\n'
# Move cursor around
printf '\033[5;5H'
printf 'Cursor at (5,5)'
printf '\033[10;10H'
printf '\033[33mYellow text at (10,10)\033[0m'
# Wait a bit
sleep 0.5
# Exit alternate screen
printf '\033[?1049l'
`

	session := NewSession(
		WithCommand("sh", "-c", fullScreenScript),
		WithTTY(true),
		WithTerminalSize(80, 24),
	)

	handler := NewWebSocketHandler(session)
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		err := handler.Handle(w, r)
		if err != nil {
			t.Logf("Handler error: %v", err)
		}
	}))
	defer server.Close()

	wsURL := strings.Replace(server.URL, "http://", "ws://", 1)
	conn, _, err := gorillaws.DefaultDialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("Failed to connect WebSocket: %v", err)
	}
	defer conn.Close()

	// Collect all output
	var output bytes.Buffer
	done := make(chan error, 1)

	go func() {
		for {
			messageType, data, err := conn.ReadMessage()
			if err != nil {
				done <- err
				return
			}
			if messageType == gorillaws.BinaryMessage {
				output.Write(data)
			}
		}
	}()

	// Wait for completion
	select {
	case <-done:
	case <-time.After(2 * time.Second):
		conn.Close()
		<-done
	}

	outputStr := output.String()

	// Verify all the control sequences are present
	sequences := []string{
		"\x1b[?1049h", // Enter alternate screen
		"\x1b[2J",     // Clear screen
		"\x1b[H",      // Cursor home
		"\x1b[5;5H",   // Move to 5,5
		"\x1b[10;10H", // Move to 10,10
		"\x1b[33m",    // Yellow color
		"\x1b[0m",     // Reset
		"\x1b[?1049l", // Exit alternate screen
	}

	for _, seq := range sequences {
		if !strings.Contains(outputStr, seq) {
			t.Errorf("Missing control sequence %q in output", seq)
			t.Logf("Output (hex): %x", outputStr)
		}
	}

	// Verify text content
	expectedTexts := []string{
		"Full Screen App Test",
		"Cursor at (5,5)",
		"Yellow text at (10,10)",
	}

	for _, text := range expectedTexts {
		if !strings.Contains(outputStr, text) {
			t.Errorf("Missing text %q in output", text)
		}
	}
}

// TestByteStreamIntegrity verifies no bytes are lost or corrupted
func TestByteStreamIntegrity(t *testing.T) {
	// This test always runs in Linux Docker environment

	// Generate test pattern with all printable ASCII characters and control sequences
	var testPattern bytes.Buffer

	// Add all printable ASCII
	for i := 32; i < 127; i++ {
		testPattern.WriteByte(byte(i))
	}
	testPattern.WriteString("\n")

	// Add common control sequences
	controlSeqs := []string{
		"\x1b[H",      // Home
		"\x1b[2J",     // Clear
		"\x1b[K",      // Clear line
		"\x1b[1m",     // Bold
		"\x1b[0m",     // Reset
		"\x1b[31m",    // Red
		"\x1b[32m",    // Green
		"\x1b[?1049h", // Alt screen on
		"\x1b[?1049l", // Alt screen off
		"\x1b7",       // Save cursor
		"\x1b8",       // Restore cursor
	}

	for _, seq := range controlSeqs {
		testPattern.WriteString(seq)
		testPattern.WriteString("TEST")
		testPattern.WriteString("\n")
	}

	// Add binary data representation
	testPattern.WriteString("Binary test: ")
	for i := 0; i < 32; i++ {
		fmt.Fprintf(&testPattern, "\\x%02x", i)
	}
	testPattern.WriteString("\n")

	// Write pattern to a temp file to avoid shell escaping issues
	tmpfile, err := os.CreateTemp("", "test-pattern-*.bin")
	if err != nil {
		t.Fatal(err)
	}
	defer os.Remove(tmpfile.Name())

	if _, err := tmpfile.Write(testPattern.Bytes()); err != nil {
		t.Fatal(err)
	}
	tmpfile.Close()

	session := NewSession(
		WithCommand("cat", tmpfile.Name()),
		WithTTY(true),
		WithTerminalSize(120, 40),
	)

	handler := NewWebSocketHandler(session)
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		err := handler.Handle(w, r)
		if err != nil {
			t.Logf("Handler error: %v", err)
		}
	}))
	defer server.Close()

	wsURL := strings.Replace(server.URL, "http://", "ws://", 1)
	conn, _, err := gorillaws.DefaultDialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("Failed to connect WebSocket: %v", err)
	}
	defer conn.Close()

	var received bytes.Buffer
	done := make(chan error, 1)

	go func() {
		for {
			messageType, data, err := conn.ReadMessage()
			if err != nil {
				done <- err
				return
			}
			if messageType == gorillaws.BinaryMessage {
				received.Write(data)
			}
		}
	}()

	select {
	case <-done:
	case <-time.After(2 * time.Second):
		conn.Close()
		<-done
	}

	// Verify all printable ASCII characters are present
	receivedStr := received.String()
	for i := 32; i < 127; i++ {
		if !strings.Contains(receivedStr, string(rune(i))) {
			t.Errorf("Missing ASCII character %d (%c)", i, i)
		}
	}

	// Verify all control sequences
	for _, seq := range controlSeqs {
		if !strings.Contains(receivedStr, seq) {
			t.Errorf("Missing control sequence %q", seq)
		}
	}
}
