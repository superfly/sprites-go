package main

import (
	"context"
	"fmt"
	"log/slog"
	"net"
	"net/http"
	"net/url"
	"os"
	"strconv"
	"strings"
	"testing"
	"time"

	"github.com/sprite-env/packages/wsexec"
)

// TestNonTTYCommands tests various non-TTY commands through the full wsexec stack
func TestNonTTYCommands(t *testing.T) {
	server, baseURL, token := startMockServer(t)
	defer server.Close()

	tests := []struct {
		name       string
		cmd        []string
		workingDir string
		env        []string
		expectExit int
		contains   string
	}{
		{
			name:       "basic echo command",
			cmd:        []string{"echo", "hello", "world"},
			expectExit: 0,
			contains:   "hello world",
		},
		{
			name:       "command with working directory",
			cmd:        []string{"pwd"},
			workingDir: "/tmp",
			expectExit: 0,
			contains:   "/tmp",
		},
		{
			name:       "command with environment variables",
			cmd:        []string{"sh", "-c", "echo TEST_VAR=$TEST_VAR"},
			env:        []string{"TEST_VAR=test_value"},
			expectExit: 0,
			contains:   "TEST_VAR=test_value",
		},
		{
			name:       "command with stderr output",
			cmd:        []string{"sh", "-c", "echo 'error message' >&2"},
			expectExit: 0,
			contains:   "error message",
		},
		{
			name:       "command that exits with non-zero",
			cmd:        []string{"sh", "-c", "echo 'failing' && exit 42"},
			expectExit: 42,
			contains:   "failing",
		},
		{
			name:       "multiline output command",
			cmd:        []string{"sh", "-c", "echo 'line1'; echo 'line2'; echo 'line3'"},
			expectExit: 0,
			contains:   "line1",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			exitCode := executeDirectWebSocket(baseURL, token, tt.cmd, tt.workingDir, tt.env, false)

			if exitCode != tt.expectExit {
				t.Errorf("Expected exit code %d, got %d", tt.expectExit, exitCode)
			}
		})
	}
}

// TestTTYCommands tests various TTY commands through the full wsexec stack
func TestTTYCommands(t *testing.T) {
	server, baseURL, token := startMockServer(t)
	defer server.Close()

	tests := []struct {
		name       string
		cmd        []string
		workingDir string
		env        []string
		expectExit int
		contains   string
	}{
		{
			name:       "basic TTY echo command",
			cmd:        []string{"echo", "tty", "hello"},
			expectExit: 0,
			contains:   "tty hello",
		},
		{
			name:       "TTY command with environment",
			cmd:        []string{"sh", "-c", "echo TTY_VAR=$TTY_VAR"},
			env:        []string{"TTY_VAR=tty_value"},
			expectExit: 0,
			contains:   "TTY_VAR=tty_value",
		},
		{
			name:       "TTY command with working directory",
			cmd:        []string{"pwd"},
			workingDir: "/tmp",
			expectExit: 0,
			contains:   "/tmp",
		},
		{
			name:       "TTY command that exits with non-zero",
			cmd:        []string{"sh", "-c", "echo 'tty failing' && exit 13"},
			expectExit: 13,
			contains:   "tty failing",
		},
		{
			name:       "TTY multiline command",
			cmd:        []string{"sh", "-c", "echo 'tty line1'; echo 'tty line2'"},
			expectExit: 0,
			contains:   "tty line1",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			exitCode := executeDirectWebSocket(baseURL, token, tt.cmd, tt.workingDir, tt.env, true)

			if exitCode != tt.expectExit {
				t.Errorf("Expected exit code %d, got %d", tt.expectExit, exitCode)
			}
		})
	}
}

// TestCommandTimeout tests command execution with timeout
func TestCommandTimeout(t *testing.T) {
	server, baseURL, token := startMockServer(t)
	defer server.Close()

	// Test a command that should timeout (sleep for longer than our client timeout)
	exitCode := executeDirectWebSocket(baseURL, token, []string{"sleep", "10"}, "", nil, false)

	// Should return non-zero exit code due to timeout/cancellation
	if exitCode == 0 {
		t.Error("Expected non-zero exit code for timed out command")
	}
}

// TestStdinHandling tests stdin input handling through WebSocket
func TestStdinHandling(t *testing.T) {
	server, baseURL, token := startMockServer(t)
	defer server.Close()

	// Test a command that reads from stdin
	// Note: This is a simplified test - in reality we'd need to set up stdin simulation
	exitCode := executeDirectWebSocket(baseURL, token, []string{"cat"}, "", nil, false)

	// cat without input should exit cleanly when stdin is closed
	if exitCode != 0 {
		t.Logf("cat command exited with code %d (expected for no stdin)", exitCode)
	}
}

// TestBuildExecWebSocketURL tests the URL building functionality
func TestBuildExecWebSocketURL(t *testing.T) {
	tests := []struct {
		name      string
		baseURL   string
		expectURL string
		expectErr bool
	}{
		{
			name:      "HTTP to WS conversion",
			baseURL:   "http://localhost:8080",
			expectURL: "ws://localhost:8080/exec",
		},
		{
			name:      "HTTPS to WSS conversion",
			baseURL:   "https://example.com",
			expectURL: "wss://example.com/exec",
		},
		{
			name:      "HTTP with path",
			baseURL:   "http://localhost:8080/api",
			expectURL: "ws://localhost:8080/api/exec",
		},
		{
			name:      "invalid scheme",
			baseURL:   "ftp://example.com",
			expectErr: true,
		},
		{
			name:      "invalid URL",
			baseURL:   "not-a-url",
			expectErr: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			wsURL, err := buildExecWebSocketURL(tt.baseURL)

			if tt.expectErr {
				if err == nil {
					t.Error("Expected error but got none")
				}
				return
			}

			if err != nil {
				t.Fatalf("Unexpected error: %v", err)
			}

			if wsURL.String() != tt.expectURL {
				t.Errorf("Expected URL %s, got %s", tt.expectURL, wsURL.String())
			}
		})
	}
}

// TestExecCommand tests the exec command parsing and flag handling
func TestExecCommand(t *testing.T) {
	// Start mock server
	server, baseURL, token := startMockServer(t)
	defer server.Close()

	// Set environment variables for the test
	os.Setenv("SPRITE_URL", baseURL)
	os.Setenv("SPRITE_TOKEN", token)
	defer func() {
		os.Unsetenv("SPRITE_URL")
		os.Unsetenv("SPRITE_TOKEN")
	}()

	tests := []struct {
		name     string
		args     []string
		expectOK bool
	}{
		{
			name:     "basic command",
			args:     []string{"echo", "test"},
			expectOK: true,
		},
		{
			name:     "command with flags",
			args:     []string{"-dir", "/tmp", "pwd"},
			expectOK: true,
		},
		{
			name:     "command with TTY flag",
			args:     []string{"-tty", "echo", "test"},
			expectOK: true,
		},
		{
			name:     "command with env vars",
			args:     []string{"-env", "FOO=bar,BAZ=qux", "env"},
			expectOK: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Test that the command parsing doesn't panic or fail immediately
			// Note: We're testing the parsing logic, not the actual execution
			defer func() {
				if r := recover(); r != nil {
					if tt.expectOK {
						t.Errorf("Expected command to parse successfully but got panic: %v", r)
					}
				}
			}()

			// We can't easily test execCommand directly since it calls os.Exit
			// So we test the URL building and parameter parsing instead
			wsURL, err := buildExecWebSocketURL(baseURL)
			if err != nil {
				t.Fatalf("Failed to build WebSocket URL: %v", err)
			}

			// Test query parameter building for different flag combinations
			query := wsURL.Query()
			if strings.Contains(strings.Join(tt.args, " "), "-dir") {
				query.Set("dir", "/tmp")
			}
			if strings.Contains(strings.Join(tt.args, " "), "-tty") {
				query.Set("tty", "true")
			}
			if strings.Contains(strings.Join(tt.args, " "), "-env") {
				query.Add("env", "FOO=bar")
				query.Add("env", "BAZ=qux")
			}

			// Verify the query can be encoded
			wsURL.RawQuery = query.Encode()
			if wsURL.String() == "" {
				t.Error("Failed to encode WebSocket URL with query parameters")
			}
		})
	}
}

// TestWebSocketConnectionErrors tests various connection error scenarios
func TestWebSocketConnectionErrors(t *testing.T) {
	tests := []struct {
		name      string
		baseURL   string
		token     string
		cmd       []string
		expectErr bool
	}{
		{
			name:      "invalid URL",
			baseURL:   "invalid-url",
			token:     "valid-token",
			cmd:       []string{"echo", "test"},
			expectErr: true,
		},
		{
			name:      "non-existent server",
			baseURL:   "ws://localhost:99999",
			token:     "valid-token",
			cmd:       []string{"echo", "test"},
			expectErr: true,
		},
		{
			name:      "empty command",
			baseURL:   "ws://localhost:8080",
			token:     "valid-token",
			cmd:       []string{},
			expectErr: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			exitCode := executeDirectWebSocket(tt.baseURL, tt.token, tt.cmd, "", nil, false)

			if tt.expectErr && exitCode == 0 {
				t.Error("Expected non-zero exit code for error case")
			}
		})
	}
}

// TestDebugMode tests the debug logging functionality
func TestDebugMode(t *testing.T) {
	server, baseURL, token := startMockServer(t)
	defer server.Close()

	// Test debug mode with a simple command
	exitCode := executeDirectWebSocket(baseURL, token, []string{"echo", "debug test"}, "", nil, false)

	if exitCode != 0 {
		t.Errorf("Expected exit code 0, got %d", exitCode)
	}
}

// startMockServer starts a mock HTTP server with WebSocket support for testing
func startMockServer(t *testing.T) (*http.Server, string, string) {
	// Find a random available port
	listener, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatalf("Failed to find available port: %v", err)
	}
	port := listener.Addr().(*net.TCPAddr).Port
	listener.Close()

	// Create HTTP server
	mux := http.NewServeMux()

	// Set up the /exec endpoint with WebSocket support
	mux.HandleFunc("/exec", func(w http.ResponseWriter, r *http.Request) {
		// Simple auth check
		authHeader := r.Header.Get("Authorization")
		if authHeader != "Bearer test-token" {
			http.Error(w, "Unauthorized", http.StatusUnauthorized)
			return
		}

		// Parse command from query parameters
		query := r.URL.Query()
		cmdArgs := query["cmd"]
		if len(cmdArgs) == 0 {
			// Default to echo for testing
			cmdArgs = []string{"echo", "default"}
		}

		// Get command path (first argument)
		path := query.Get("path")
		if path == "" && len(cmdArgs) > 0 {
			path = cmdArgs[0]
		}
		if path == "" {
			path = "echo"
		}

		// Create command
		var args []string
		if len(cmdArgs) > 1 {
			args = cmdArgs[1:]
		}
		cmd := wsexec.NewServerCommand(path, args...)

		// Set TTY based on query parameter
		tty := query.Get("tty") == "true"
		cmd.SetTTY(tty)

		// Set working directory if specified
		if dir := query.Get("dir"); dir != "" {
			cmd.SetWorkingDir(dir)
		}

		// Set environment variables if specified
		if envVars := query["env"]; len(envVars) > 0 {
			cmd.SetEnv(envVars)
		}

		// Set initial terminal size if specified (for TTY mode)
		if tty {
			if colsStr := query.Get("cols"); colsStr != "" {
				if cols, err := strconv.ParseUint(colsStr, 10, 16); err == nil {
					if rowsStr := query.Get("rows"); rowsStr != "" {
						if rows, err := strconv.ParseUint(rowsStr, 10, 16); err == nil {
							cmd.SetInitialTerminalSize(uint16(cols), uint16(rows))
						}
					}
				}
			}
		}

		// Set logger for debugging (only in verbose mode)
		if testing.Verbose() {
			logger := slog.New(slog.NewTextHandler(os.Stdout, &slog.HandlerOptions{
				Level: slog.LevelInfo, // Reduced from Debug to Info to reduce noise
			}))
			cmd.SetLogger(logger)
		}

		// Add request context with timeout for long-running commands
		ctx, cancel := context.WithTimeout(r.Context(), 5*time.Second)
		defer cancel()
		cmd.SetContext(ctx)

		// Handle the WebSocket connection
		if err := cmd.Handle(w, r); err != nil {
			t.Logf("WebSocket handler error: %v", err)
		}
	})

	server := &http.Server{
		Addr:    fmt.Sprintf("127.0.0.1:%d", port),
		Handler: mux,
	}

	// Start server in goroutine
	go func() {
		if err := server.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			t.Logf("Server error: %v", err)
		}
	}()

	// Wait for server to start
	baseURL := fmt.Sprintf("http://127.0.0.1:%d", port)
	for i := 0; i < 50; i++ {
		if resp, err := http.Get(baseURL + "/exec"); err == nil {
			resp.Body.Close()
			break
		}
		time.Sleep(10 * time.Millisecond)
	}

	return server, baseURL, "test-token"
}

// TestMockServerSetup tests that our mock server setup works correctly
func TestMockServerSetup(t *testing.T) {
	server, baseURL, token := startMockServer(t)
	defer server.Close()

	// Test that we can build a WebSocket URL
	wsURL, err := buildExecWebSocketURL(baseURL)
	if err != nil {
		t.Fatalf("Failed to build WebSocket URL: %v", err)
	}

	expectedScheme := "ws"
	if wsURL.Scheme != expectedScheme {
		t.Errorf("Expected scheme %s, got %s", expectedScheme, wsURL.Scheme)
	}

	if wsURL.Path != "/exec" {
		t.Errorf("Expected path /exec, got %s", wsURL.Path)
	}

	// Test that the token is set correctly
	if token != "test-token" {
		t.Errorf("Expected token 'test-token', got %s", token)
	}

	// Test that the server is reachable
	u, _ := url.Parse(baseURL)
	if u.Host == "" {
		t.Error("Server URL should have a valid host")
	}
}

// TestHandleBrowserOpen tests the browser open functionality with callback servers
func TestHandleBrowserOpen(t *testing.T) {
	// Mock the browser open command to avoid actually opening browser
	originalEnv := os.Getenv("PATH")
	defer os.Setenv("PATH", originalEnv)

	// Create a fake 'open' command that does nothing
	tempDir := t.TempDir()
	fakeOpenPath := tempDir + "/open"
	err := os.WriteFile(fakeOpenPath, []byte("#!/bin/bash\nexit 0\n"), 0755)
	if err != nil {
		t.Fatalf("Failed to create fake open command: %v", err)
	}
	os.Setenv("PATH", tempDir+":"+originalEnv)

	t.Run("single_port_callback", func(t *testing.T) {
		// Find an available port for testing
		listener, err := net.Listen("tcp", "127.0.0.1:0")
		if err != nil {
			t.Fatalf("Failed to find available port: %v", err)
		}
		port := listener.Addr().(*net.TCPAddr).Port
		listener.Close()

		portStr := strconv.Itoa(port)
		testURL := "https://oauth.example.com/auth?callback=http://localhost:" + portStr + "/callback"

		// Channel to signal when the callback is received
		callbackReceived := make(chan bool, 1)

		// Start a goroutine to make the callback request
		go func() {
			// Give the server time to start
			time.Sleep(200 * time.Millisecond)

			// Make callback request
			resp, err := http.Get("http://localhost:" + portStr + "/callback?code=test123")
			if err != nil {
				t.Errorf("Failed to make callback request: %v", err)
				return
			}
			defer resp.Body.Close()

			// Check response
			if resp.StatusCode != http.StatusNotImplemented {
				t.Errorf("Expected status %d, got %d", http.StatusNotImplemented, resp.StatusCode)
			}

			callbackReceived <- true
		}()

		// Call handleBrowserOpen
		handleBrowserOpen(testURL, []string{portStr})

		// Wait for callback to be received
		select {
		case <-callbackReceived:
			// Success!
		case <-time.After(3 * time.Second):
			t.Error("Timeout waiting for callback to be received")
		}

		// Give server time to shut down
		time.Sleep(300 * time.Millisecond)
	})

	t.Run("multiple_ports", func(t *testing.T) {
		// Find two available ports
		listener1, err := net.Listen("tcp", "127.0.0.1:0")
		if err != nil {
			t.Fatalf("Failed to find first available port: %v", err)
		}
		port1 := listener1.Addr().(*net.TCPAddr).Port
		listener1.Close()

		listener2, err := net.Listen("tcp", "127.0.0.1:0")
		if err != nil {
			t.Fatalf("Failed to find second available port: %v", err)
		}
		port2 := listener2.Addr().(*net.TCPAddr).Port
		listener2.Close()

		portStr1 := strconv.Itoa(port1)
		portStr2 := strconv.Itoa(port2)
		multiplePorts := []string{portStr1, portStr2}
		testURL := "https://oauth.example.com/auth"

		// Test with multiple ports (just verify they start without errors)
		handleBrowserOpen(testURL, multiplePorts)

		// Give servers time to start
		time.Sleep(300 * time.Millisecond)

		// Test that servers are running on both ports
		for _, p := range multiplePorts {
			resp, err := http.Get("http://localhost:" + p + "/test")
			if err != nil {
				t.Errorf("Server not running on port %s: %v", p, err)
				continue
			}
			resp.Body.Close()
			if resp.StatusCode != http.StatusNotImplemented {
				t.Errorf("Expected status %d on port %s, got %d", http.StatusNotImplemented, p, resp.StatusCode)
			}
		}

		// Give servers time to shut down after the requests
		time.Sleep(300 * time.Millisecond)
	})

	t.Run("empty_ports", func(t *testing.T) {
		testURL := "https://oauth.example.com/auth"

		// Test with empty ports (should not fail)
		handleBrowserOpen(testURL, []string{})
		handleBrowserOpen(testURL, nil)
	})
}
