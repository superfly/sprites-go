package tests

import (
	"encoding/json"
	"fmt"
	"net/http"
	"net/url"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	gorillaws "github.com/gorilla/websocket"
)

// TestExecIntegration tests the /exec endpoint through a real sprite-env server
func TestExecIntegration(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	// Build and start the test container
	containerID, cleanup := setupTestContainer(t)
	defer cleanup()

	// Wait for server to be ready
	waitForServer(t, containerID)

	// Get the API token from the container
	token := getAPIToken(t, containerID)

	// Run test cases
	t.Run("BasicCommand", func(t *testing.T) {
		testBasicCommand(t, containerID, token)
	})

	t.Run("TTYMode", func(t *testing.T) {
		testTTYMode(t, containerID, token)
	})

	t.Run("LargeOutput", func(t *testing.T) {
		testLargeOutput(t, containerID, token)
	})

	t.Run("EnvironmentVariables", func(t *testing.T) {
		testEnvironmentVariables(t, containerID, token)
	})

	t.Run("WorkingDirectory", func(t *testing.T) {
		testWorkingDirectory(t, containerID, token)
	})

	t.Run("ExitCodes", func(t *testing.T) {
		testExitCodes(t, containerID, token)
	})

	// Test basic WebSocket connection
	t.Run("BasicWebSocketConnection", func(t *testing.T) {
		testBasicWebSocketConnection(t, containerID)
	})

	// Test long-running TTY bash session
	t.Run("LongRunningTTYBash", func(t *testing.T) {
		testLongRunningTTYBash(t, containerID, token)
	})

	// Test interactive TTY bash session
	t.Run("InteractiveTTYBash", func(t *testing.T) {
		testInteractiveTTYBash(t, containerID, token)
	})

	// New: Ensure port watcher messages arrive over WebSocket
	t.Run("PortNotifications", func(t *testing.T) {
		testPortNotifications(t, containerID, token)
	})
}

func testBasicWebSocketConnection(t *testing.T, containerID string) {
	// Test that we can connect to the server by checking if it's listening
	resp, err := http.Get("http://localhost:8080/")
	if err != nil {
		t.Fatalf("Failed to connect to server: %v", err)
	}
	defer resp.Body.Close()

	// Any response means the server is running (even 404 is OK)
	t.Logf("Successfully connected to server (status: %d)", resp.StatusCode)
}

func setupTestContainer(t *testing.T) (string, func()) {
	// Check if Docker is available
	if _, err := exec.LookPath("docker"); err != nil {
		t.Skip("Docker not available, skipping integration test")
	}

	// Build the test image
	buildCmd := exec.Command("docker", "build", "-f", "Dockerfile.test", "-t", "sprite-test", ".")
	buildCmd.Dir = "."
	buildOutput, err := buildCmd.CombinedOutput()
	if err != nil {
		t.Fatalf("Failed to build test image: %v\nOutput: %s", err, buildOutput)
	}

	// Get absolute path to parent directory
	parentDir, err := filepath.Abs("../")
	if err != nil {
		t.Fatalf("Failed to get absolute path: %v", err)
	}

	// Start the container with volume mount
	runCmd := exec.Command("docker", "run", "-d", "-p", "8080:8080", "-v", parentDir+":/workspace", "--name", "sprite-test-container", "sprite-test")
	runOutput, err := runCmd.CombinedOutput()
	if err != nil {
		t.Fatalf("Failed to start test container: %v\nOutput: %s", err, runOutput)
	}

	containerID := strings.TrimSpace(string(runOutput))

	cleanup := func() {
		exec.Command("docker", "stop", containerID).Run()
		exec.Command("docker", "rm", containerID).Run()
	}

	return containerID, cleanup
}

func waitForServer(t *testing.T, containerID string) {
	// Wait for server to start (port 8080)
	maxRetries := 600
	for i := 0; i < maxRetries; i++ {
		time.Sleep(1 * time.Second)

		cmd := exec.Command("docker", "exec", containerID, "ss", "-ltn")
		if output, err := cmd.CombinedOutput(); err == nil {
			if strings.Contains(string(output), ":8080") {
				t.Log("Server is ready")
				return
			}
		}
	}
	t.Fatal("Server failed to start within timeout")
}

func getAPIToken(t *testing.T, containerID string) string {
	// Extract token from the server config or logs
	// For now, use a default test token
	return "test-token-12345"
}

func testBasicCommand(t *testing.T, containerID, token string) {
	// Test simple echo command
	cmd := []string{"echo", "hello world"}
	wsURL := buildWebSocketURL(cmd, "")

	headers := http.Header{}
	headers.Set("Authorization", "Bearer "+token)

	conn, _, err := gorillaws.DefaultDialer.Dial(wsURL, headers)
	if err != nil {
		t.Fatalf("Failed to connect: %v", err)
	}
	defer conn.Close()

	var output strings.Builder
	done := make(chan struct{})

	go func() {
		defer close(done)
		for {
			messageType, data, err := conn.ReadMessage()
			if err != nil {
				return
			}

			if messageType == gorillaws.BinaryMessage && len(data) > 0 {
				stream := data[0]
				payload := data[1:]

				if stream == 1 { // stdout
					output.Write(payload)
				} else if stream == 3 { // exit
					return
				}
			}
		}
	}()

	select {
	case <-done:
	case <-time.After(5 * time.Second):
		t.Fatal("timeout")
	}

	expected := "hello world\n"
	if output.String() != expected {
		t.Errorf("Expected %q, got %q", expected, output.String())
	}
}

func testTTYMode(t *testing.T, containerID, token string) {
	// Test TTY mode with color output using interactive session
	session := NewInteractiveTTYSession(t, containerID, token, []string{"/bin/sh"})
	defer session.Close()

	// Wait for shell prompt
	if err := session.WaitForOutput("#", 5*time.Second); err != nil {
		t.Fatalf("Failed to get shell prompt: %v", err)
	}

	// Send color output command
	if err := session.SendInput("printf '\\033[31mRED\\033[0m\\n'\r\n"); err != nil {
		t.Fatalf("Failed to send command: %v", err)
	}

	// Wait for output and prompt
	if err := session.WaitForOutput("#", 5*time.Second); err != nil {
		t.Fatalf("Failed to get output: %v", err)
	}

	// Exit shell
	if err := session.SendInput("exit\r\n"); err != nil {
		t.Fatalf("Failed to send exit command: %v", err)
	}
}

func testLargeOutput(t *testing.T, containerID, token string) {
	// Test large output handling
	cmd := []string{"sh", "-c", "for i in $(seq 1 1000); do echo 'line $i'; done"}
	wsURL := buildWebSocketURL(cmd, "")

	headers := http.Header{}
	headers.Set("Authorization", "Bearer "+token)

	conn, _, err := gorillaws.DefaultDialer.Dial(wsURL, headers)
	if err != nil {
		t.Fatalf("Failed to connect: %v", err)
	}
	defer conn.Close()

	var output strings.Builder
	done := make(chan struct{})

	go func() {
		defer close(done)
		for {
			messageType, data, err := conn.ReadMessage()
			if err != nil {
				return
			}

			if messageType == gorillaws.BinaryMessage && len(data) > 0 {
				stream := data[0]
				payload := data[1:]

				if stream == 1 { // stdout
					output.Write(payload)
				} else if stream == 3 { // exit
					return
				}
			}
		}
	}()

	select {
	case <-done:
	case <-time.After(30 * time.Second):
		t.Fatal("timeout")
	}

	// Should have received all 1000 lines
	lines := strings.Split(strings.TrimSpace(output.String()), "\n")
	if len(lines) != 1000 {
		t.Errorf("Expected 1000 lines, got %d", len(lines))
	}
}

func testEnvironmentVariables(t *testing.T, containerID, token string) {
	// Test environment variable handling
	cmd := []string{"env"}
	wsURL := buildWebSocketURL(cmd, "") + "&env=TEST_VAR=test_value"

	headers := http.Header{}
	headers.Set("Authorization", "Bearer "+token)

	conn, _, err := gorillaws.DefaultDialer.Dial(wsURL, headers)
	if err != nil {
		t.Fatalf("Failed to connect: %v", err)
	}
	defer conn.Close()

	var output strings.Builder
	done := make(chan struct{})

	go func() {
		defer close(done)
		for {
			messageType, data, err := conn.ReadMessage()
			if err != nil {
				return
			}

			if messageType == gorillaws.BinaryMessage && len(data) > 0 {
				stream := data[0]
				payload := data[1:]

				if stream == 1 { // stdout
					output.Write(payload)
				} else if stream == 3 { // exit
					return
				}
			}
		}
	}()

	select {
	case <-done:
	case <-time.After(5 * time.Second):
		t.Fatal("timeout")
	}

	if !strings.Contains(output.String(), "TEST_VAR=test_value") {
		t.Error("Environment variable not found in output")
	}
}

func testWorkingDirectory(t *testing.T, containerID, token string) {
	// Test working directory setting
	cmd := []string{"pwd"}
	wsURL := buildWebSocketURL(cmd, "") + "&dir=/tmp"

	headers := http.Header{}
	headers.Set("Authorization", "Bearer "+token)

	conn, _, err := gorillaws.DefaultDialer.Dial(wsURL, headers)
	if err != nil {
		t.Fatalf("Failed to connect: %v", err)
	}
	defer conn.Close()

	var output strings.Builder
	done := make(chan struct{})

	go func() {
		defer close(done)
		for {
			messageType, data, err := conn.ReadMessage()
			if err != nil {
				return
			}

			if messageType == gorillaws.BinaryMessage && len(data) > 0 {
				stream := data[0]
				payload := data[1:]

				if stream == 1 { // stdout
					output.Write(payload)
				} else if stream == 3 { // exit
					return
				}
			}
		}
	}()

	select {
	case <-done:
	case <-time.After(5 * time.Second):
		t.Fatal("timeout")
	}

	if !strings.Contains(output.String(), "/tmp") {
		t.Error("Working directory not set correctly")
	}
}

func testExitCodes(t *testing.T, containerID, token string) {
	testCases := []struct {
		name     string
		command  []string
		expected int
	}{
		{"success", []string{"echo", "success"}, 0},
		{"failure", []string{"sh", "-c", "exit 42"}, 42},
		{"command_not_found", []string{"nonexistent_command"}, 255}, // Alpine sh returns 255 for command not found
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			wsURL := buildWebSocketURL(tc.command, "")

			headers := http.Header{}
			headers.Set("Authorization", "Bearer "+token)

			conn, _, err := gorillaws.DefaultDialer.Dial(wsURL, headers)
			if err != nil {
				t.Fatalf("Failed to connect: %v", err)
			}
			defer conn.Close()

			var exitCode int
			done := make(chan struct{})

			go func() {
				defer close(done)
				for {
					messageType, data, err := conn.ReadMessage()
					if err != nil {
						return
					}

					if messageType == gorillaws.BinaryMessage && len(data) > 0 {
						stream := data[0]
						payload := data[1:]

						if stream == 3 { // exit
							if len(payload) > 0 {
								exitCode = int(payload[0])
							}
							return
						}
					}
				}
			}()

			select {
			case <-done:
			case <-time.After(5 * time.Second):
				t.Fatal("timeout")
			}

			if exitCode != tc.expected {
				t.Errorf("Expected exit code %d, got %d", tc.expected, exitCode)
			}
		})
	}
}

func buildWebSocketURL(cmd []string, token string) string {
	baseURL := "ws://localhost:8080/exec"

	// Add command parameters (token is now passed in Authorization header)
	var params []string
	if token != "" {
		params = append(params, fmt.Sprintf("token=%s", token))
	}
	for _, arg := range cmd {
		params = append(params, fmt.Sprintf("cmd=%s", url.QueryEscape(arg)))
	}

	if len(params) > 0 {
		return baseURL + "?" + strings.Join(params, "&")
	}
	return baseURL
}

func testLongRunningTTYBash(t *testing.T, containerID, token string) {
	// Test 1: Basic command execution
	t.Run("BasicCommand", func(t *testing.T) {
		t.Logf("Testing basic command execution")
		cmd := []string{"echo", "hello world"}
		wsURL := buildWebSocketURL(cmd, "")

		headers := http.Header{}
		headers.Set("Authorization", "Bearer "+token)

		conn, resp, err := gorillaws.DefaultDialer.Dial(wsURL, headers)
		if err != nil {
			t.Fatalf("Failed to connect to WebSocket: %v, response: %+v", err, resp)
		}
		defer conn.Close()

		// Set up message handling
		done := make(chan struct{})
		var receivedMessages []string

		go func() {
			defer close(done)
			for {
				messageType, message, err := conn.ReadMessage()
				if err != nil {
					if gorillaws.IsUnexpectedCloseError(err, gorillaws.CloseNormalClosure, gorillaws.CloseGoingAway) {
						t.Errorf("Unexpected WebSocket close: %v", err)
					}
					return
				}

				if messageType == gorillaws.BinaryMessage && len(message) > 0 {
					stream := message[0]
					payload := message[1:]

					if stream == 1 { // stdout
						msgStr := string(payload)
						receivedMessages = append(receivedMessages, msgStr)
						t.Logf("Received stdout: %q", msgStr)
					} else if stream == 3 { // exit
						t.Logf("Received exit signal")
						return
					}
				} else if messageType == gorillaws.TextMessage {
					msgStr := string(message)
					receivedMessages = append(receivedMessages, msgStr)
					t.Logf("Received text: %q", msgStr)
				}
			}
		}()

		// Wait for the command to complete
		select {
		case <-done:
			t.Logf("Command completed")
		case <-time.After(10 * time.Second):
			t.Fatal("Command timed out")
		}

		// Check if we got the expected output
		if !containsAny(receivedMessages, "hello world") {
			t.Errorf("Expected 'hello world' in output, got: %v", receivedMessages)
		}

		t.Logf("Basic command execution test completed successfully. Total messages received: %d", len(receivedMessages))
	})

	// Test 2: Large output handling
	t.Run("LargeOutput", func(t *testing.T) {
		t.Logf("Testing large output handling")
		cmd := []string{"sh", "-c", "for i in $(seq 1 100); do echo 'line $i'; done"}
		wsURL := buildWebSocketURL(cmd, "")

		headers := http.Header{}
		headers.Set("Authorization", "Bearer "+token)

		conn, resp, err := gorillaws.DefaultDialer.Dial(wsURL, headers)
		if err != nil {
			t.Fatalf("Failed to connect to WebSocket: %v, response: %+v", err, resp)
		}
		defer conn.Close()

		// Set up message handling
		done := make(chan struct{})
		var output strings.Builder

		go func() {
			defer close(done)
			for {
				messageType, message, err := conn.ReadMessage()
				if err != nil {
					if gorillaws.IsUnexpectedCloseError(err, gorillaws.CloseNormalClosure, gorillaws.CloseGoingAway) {
						t.Errorf("Unexpected WebSocket close: %v", err)
					}
					return
				}

				if messageType == gorillaws.BinaryMessage && len(message) > 0 {
					stream := message[0]
					payload := message[1:]

					if stream == 1 { // stdout
						output.Write(payload)
					} else if stream == 3 { // exit
						t.Logf("Received exit signal")
						return
					}
				}
			}
		}()

		// Wait for the command to complete
		select {
		case <-done:
			t.Logf("Command completed")
		case <-time.After(30 * time.Second):
			t.Fatal("Command timed out")
		}

		// Check if we got the expected output
		outputStr := output.String()
		lines := strings.Split(strings.TrimSpace(outputStr), "\n")
		if len(lines) != 100 {
			t.Errorf("Expected 100 lines, got %d", len(lines))
		}

		t.Logf("Large output test completed successfully. Received %d lines", len(lines))
	})

	// Test 3: Error output handling
	t.Run("ErrorOutput", func(t *testing.T) {
		t.Logf("Testing error output handling")
		cmd := []string{"sh", "-c", "echo 'stdout message' && echo 'stderr message' >&2"}
		wsURL := buildWebSocketURL(cmd, "")

		headers := http.Header{}
		headers.Set("Authorization", "Bearer "+token)

		conn, resp, err := gorillaws.DefaultDialer.Dial(wsURL, headers)
		if err != nil {
			t.Fatalf("Failed to connect to WebSocket: %v, response: %+v", err, resp)
		}
		defer conn.Close()

		// Set up message handling
		done := make(chan struct{})
		var stdout, stderr strings.Builder

		go func() {
			defer close(done)
			for {
				messageType, message, err := conn.ReadMessage()
				if err != nil {
					if gorillaws.IsUnexpectedCloseError(err, gorillaws.CloseNormalClosure, gorillaws.CloseGoingAway) {
						t.Errorf("Unexpected WebSocket close: %v", err)
					}
					return
				}

				if messageType == gorillaws.BinaryMessage && len(message) > 0 {
					stream := message[0]
					payload := message[1:]

					if stream == 1 { // stdout
						stdout.Write(payload)
						t.Logf("Received stdout: %q", string(payload))
					} else if stream == 2 { // stderr
						stderr.Write(payload)
						t.Logf("Received stderr: %q", string(payload))
					} else if stream == 3 { // exit
						t.Logf("Received exit signal")
						return
					}
				}
			}
		}()

		// Wait for the command to complete
		select {
		case <-done:
			t.Logf("Command completed")
		case <-time.After(10 * time.Second):
			t.Fatal("Command timed out")
		}

		// Check if we got the expected output
		if !strings.Contains(stdout.String(), "stdout message") {
			t.Errorf("Expected 'stdout message' in stdout, got: %q", stdout.String())
		}
		if !strings.Contains(stderr.String(), "stderr message") {
			t.Errorf("Expected 'stderr message' in stderr, got: %q", stderr.String())
		}

		t.Logf("Error output test completed successfully")
	})

	// Test 4: Long-running command with timeout
	t.Run("LongRunningCommand", func(t *testing.T) {
		t.Logf("Testing long-running command")
		cmd := []string{"sleep", "5"}
		wsURL := buildWebSocketURL(cmd, "")

		headers := http.Header{}
		headers.Set("Authorization", "Bearer "+token)

		conn, resp, err := gorillaws.DefaultDialer.Dial(wsURL, headers)
		if err != nil {
			t.Fatalf("Failed to connect to WebSocket: %v, response: %+v", err, resp)
		}
		defer conn.Close()

		// Set up message handling
		done := make(chan struct{})
		var exitCode int

		go func() {
			defer close(done)
			for {
				messageType, message, err := conn.ReadMessage()
				if err != nil {
					if gorillaws.IsUnexpectedCloseError(err, gorillaws.CloseNormalClosure, gorillaws.CloseGoingAway) {
						t.Errorf("Unexpected WebSocket close: %v", err)
					}
					return
				}

				if messageType == gorillaws.BinaryMessage && len(message) > 0 {
					stream := message[0]
					payload := message[1:]

					if stream == 3 { // exit
						if len(payload) >= 4 {
							exitCode = int(payload[0]) | int(payload[1])<<8 | int(payload[2])<<16 | int(payload[3])<<24
						}
						t.Logf("Received exit signal with code: %d", exitCode)
						return
					}
				}
			}
		}()

		// Wait for the command to complete
		select {
		case <-done:
			t.Logf("Command completed with exit code: %d", exitCode)
		case <-time.After(10 * time.Second):
			t.Fatal("Command timed out")
		}

		if exitCode != 0 {
			t.Errorf("Expected exit code 0, got %d", exitCode)
		}

		t.Logf("Long-running command test completed successfully")
	})
}

// InteractiveTTYSession represents a step in an interactive TTY session
type InteractiveTTYSession struct {
	conn *gorillaws.Conn
	t    *testing.T
}

// NewInteractiveTTYSession creates a new interactive TTY session
func NewInteractiveTTYSession(t *testing.T, containerID, token string, cmd []string) *InteractiveTTYSession {
	wsURL := buildWebSocketURL(cmd, "") + "&tty=true&cols=80&rows=24"

	headers := http.Header{}
	headers.Set("Authorization", "Bearer "+token)

	conn, resp, err := gorillaws.DefaultDialer.Dial(wsURL, headers)
	if err != nil {
		t.Fatalf("Failed to connect to WebSocket: %v, response: %+v", err, resp)
	}

	return &InteractiveTTYSession{
		conn: conn,
		t:    t,
	}
}

// WaitForOutput waits for specific output to appear, with timeout
func (s *InteractiveTTYSession) WaitForOutput(expected string, timeout time.Duration) error {
	done := make(chan error, 1)
	var receivedOutput strings.Builder

	go func() {
		defer close(done)
		for {
			messageType, message, err := s.conn.ReadMessage()
			if err != nil {
				if gorillaws.IsUnexpectedCloseError(err, gorillaws.CloseNormalClosure, gorillaws.CloseGoingAway) {
					done <- fmt.Errorf("unexpected WebSocket close: %v", err)
				} else {
					done <- nil
				}
				return
			}

			if messageType == gorillaws.TextMessage {
				msgStr := string(message)
				receivedOutput.WriteString(msgStr)
				s.t.Logf("Received text: %q", msgStr)

				if expected == "" || strings.Contains(receivedOutput.String(), expected) {
					done <- nil
					return
				}
			} else if messageType == gorillaws.BinaryMessage {
				msgStr := string(message)
				receivedOutput.WriteString(msgStr)

				// Handle cursor position queries
				if strings.Contains(msgStr, "\x1b[6n") {
					// Respond with cursor position (row 1, column 1)
					response := "\x1b[1;1R"
					err := s.conn.WriteMessage(gorillaws.TextMessage, []byte(response))
					if err != nil {
						s.t.Logf("Failed to send cursor position response: %v", err)
					}
				}

				if expected == "" || strings.Contains(receivedOutput.String(), expected) {
					done <- nil
					return
				}
			}
		}
	}()

	select {
	case err := <-done:
		return err
	case <-time.After(timeout):
		return fmt.Errorf("timeout waiting for output '%s', received: %q", expected, receivedOutput.String())
	}
}

// SendInput sends input to the TTY session
func (s *InteractiveTTYSession) SendInput(input string) error {

	// Try sending as binary message with stdin stream (stream 0)
	binaryMsg := append([]byte{0}, []byte(input)...)
	err := s.conn.WriteMessage(gorillaws.BinaryMessage, binaryMsg)
	if err != nil {
		return err
	}
	return nil
}

// Close closes the TTY session
func (s *InteractiveTTYSession) Close() {
	if s.conn != nil {
		s.conn.Close()
	}
}

// ExecuteScript executes a sequence of interactive commands
func (s *InteractiveTTYSession) ExecuteScript(script []ScriptStep) error {
	for i, step := range script {
		s.t.Logf("Executing step %d: %s", i+1, step.Description)

		switch step.Type {
		case "wait":
			if err := s.WaitForOutput(step.Expected, step.Timeout); err != nil {
				return fmt.Errorf("step %d failed: %v", i+1, err)
			}
		case "send":
			if err := s.SendInput(step.Input); err != nil {
				return fmt.Errorf("step %d failed: %v", i+1, err)
			}
		case "wait_and_send":
			if err := s.WaitForOutput(step.Expected, step.Timeout); err != nil {
				return fmt.Errorf("step %d failed: %v", i+1, err)
			}
			if err := s.SendInput(step.Input); err != nil {
				return fmt.Errorf("step %d failed: %v", i+1, err)
			}
		}
	}
	return nil
}

// ScriptStep represents a single step in an interactive script
type ScriptStep struct {
	Type        string        // "wait", "send", "wait_and_send"
	Description string        // Human-readable description
	Expected    string        // Expected output to wait for
	Input       string        // Input to send
	Timeout     time.Duration // Timeout for waiting
}

func testInteractiveTTYBash(t *testing.T, containerID, token string) {
	// Create interactive TTY session with sh
	session := NewInteractiveTTYSession(t, containerID, token, []string{"/bin/sh"})
	defer session.Close()

	// Define the script to execute
	script := []ScriptStep{
		{
			Type:        "wait",
			Description: "Wait for shell prompt",
			Expected:    "#",
			Timeout:     5 * time.Second,
		},
		{
			Type:        "send",
			Description: "Send ls -la command",
			Input:       "ls -la\r\n",
		},
		{
			Type:        "wait",
			Description: "Wait for ls output and prompt",
			Expected:    "#",
			Timeout:     10 * time.Second,
		},
		{
			Type:        "send",
			Description: "Send echo command",
			Input:       "echo 'Interactive TTY test successful'\r\n",
		},
		{
			Type:        "wait",
			Description: "Wait for echo output and prompt",
			Expected:    "#",
			Timeout:     5 * time.Second,
		},
		{
			Type:        "send",
			Description: "Exit shell",
			Input:       "exit\r\n",
		},
	}

	// Execute the script
	if err := session.ExecuteScript(script); err != nil {
		t.Fatalf("Script execution failed: %v", err)
	}

	t.Logf("Interactive TTY bash session test completed successfully")
}

func containsAny(messages []string, substr string) bool {
	for _, msg := range messages {
		if strings.Contains(msg, substr) {
			return true
		}
	}
	return false
}

// testPortNotifications verifies that port_opened and port_closed messages are received
func testPortNotifications(t *testing.T, containerID, token string) {
	// Use a shell that opens and then closes a TCP listener
	// We choose a likely-free port to reduce flakiness
	port := 18088
	cmd := []string{"sh", "-c", fmt.Sprintf("nc -l 127.0.0.1 %d >/dev/null & NC_PID=$!; echo NC:$NC_PID; sleep 2; kill $NC_PID; wait $NC_PID 2>/dev/null || true; sleep 2", port)}
	wsURL := buildWebSocketURL(cmd, "")

	headers := http.Header{}
	headers.Set("Authorization", "Bearer "+token)

	conn, resp, err := gorillaws.DefaultDialer.Dial(wsURL, headers)
	if err != nil {
		t.Fatalf("Failed to connect: %v (resp=%+v)", err, resp)
	}
	defer conn.Close()

	type portMsg struct {
		Type    string `json:"type"`
		Port    int    `json:"port"`
		Address string `json:"address"`
		PID     int    `json:"pid"`
	}

	opened := false
	closed := false

	done := make(chan struct{})
	go func() {
		defer close(done)
		for {
			messageType, data, err := conn.ReadMessage()
			if err != nil {
				return
			}

			if messageType == gorillaws.TextMessage {
				var m portMsg
				// The server sends JSON text messages for port notifications
				if err := json.Unmarshal(data, &m); err == nil {
					if m.Type == "port_opened" && m.Port == port {
						opened = true
					}
					if m.Type == "port_closed" && m.Port == port {
						closed = true
						return
					}
				}
			}

			if messageType == gorillaws.BinaryMessage && len(data) > 0 {
				stream := data[0]
				if stream == 3 { // exit
					return
				}
			}
		}
	}()

	select {
	case <-done:
	case <-time.After(15 * time.Second):
		t.Fatal("timeout waiting for port notifications")
	}

	if !opened {
		t.Errorf("did not receive port_opened for %d", port)
	}
	if !closed {
		t.Errorf("did not receive port_closed for %d", port)
	}
}
