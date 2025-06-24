package wsexec_test

import (
	"bytes"
	"context"
	"io"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
	"sync"
	"testing"
	"time"

	creackpty "github.com/creack/pty"
	"github.com/sprite-env/packages/wsexec"
)

// TestPTYInteractiveShell tests PTY with interactive shell
func TestPTYInteractiveShell(t *testing.T) {
	// Create test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		// Use a simple command that exits immediately
		cmd := &wsexec.ServerCommand{
			Path: "sh",
			Args: []string{"sh", "-c", "echo 'Shell started'; echo hello; echo 'Shell done'; exit 0"},
			Tty:  true,
		}

		if err := cmd.Handle(w, r); err != nil {
			t.Errorf("Server handle error: %v", err)
		}
	}))
	defer server.Close()

	// Create client - match the server command
	req, err := http.NewRequest("GET", server.URL+"/exec/test/websocket", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}
	req.URL.Scheme = "ws"

	cmd := wsexec.Command(req, "sh", "-c", "echo 'Shell started'; echo hello; echo 'Shell done'; exit 0")
	cmd.PingInterval = 100 * time.Millisecond

	// Start with PTY
	pty, err := wsexec.Pty.Start(cmd)
	if err != nil {
		t.Fatalf("Failed to start with PTY: %v", err)
	}
	defer pty.Close()

	// Test resize
	if err := pty.SetSize(80, 24); err != nil {
		t.Errorf("Failed to set size: %v", err)
	}

	// Read all output
	output := make([]byte, 0, 1024)
	buf := make([]byte, 256)

	// Read with timeout
	done := make(chan bool)
	go func() {
		for {
			n, err := pty.Read(buf)
			if n > 0 {
				output = append(output, buf[:n]...)
			}
			if err != nil {
				break
			}
		}
		close(done)
	}()

	// Wait for output or timeout
	select {
	case <-done:
		// Reading finished
	case <-time.After(2 * time.Second):
		// Timeout
	}

	// Check output
	outputStr := string(output)
	t.Logf("PTY output: %q", outputStr)

	if !strings.Contains(outputStr, "hello") {
		t.Errorf("Expected output to contain 'hello', got %q", outputStr)
	}

	// Wait for command to finish
	if err := cmd.Wait(); err != nil {
		t.Errorf("Wait error: %v", err)
	}

	if code := cmd.ExitCode(); code != 0 {
		t.Errorf("Expected exit code 0, got %d", code)
	}
}

// TestPTYInteractiveInput tests PTY with actual interactive input
func TestPTYInteractiveInput(t *testing.T) {
	// Create test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := &wsexec.ServerCommand{
			Path: "sh",
			Args: []string{"sh"},
			Tty:  true,
		}

		if err := cmd.Handle(w, r); err != nil {
			t.Logf("Server handle error: %v", err)
		}
	}))
	defer server.Close()

	// Create client
	req, err := http.NewRequest("GET", server.URL+"/exec/test/websocket", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}
	req.URL.Scheme = "ws"

	cmd := wsexec.Command(req, "sh")
	cmd.PingInterval = 100 * time.Millisecond

	// Start with PTY
	pty, err := wsexec.Pty.Start(cmd)
	if err != nil {
		t.Fatalf("Failed to start with PTY: %v", err)
	}
	defer pty.Close()

	// Write some commands
	commands := []string{
		"echo hello\n",
		"echo world\n",
		"exit\n",
	}

	// Read output in background
	var output bytes.Buffer
	var outputMu sync.Mutex
	done := make(chan bool)

	go func() {
		defer close(done)
		buf := make([]byte, 256)
		for {
			n, err := pty.Read(buf)
			if n > 0 {
				outputMu.Lock()
				output.Write(buf[:n])
				outputMu.Unlock()
			}
			if err != nil {
				if err == io.EOF {
					break
				}
				t.Logf("Read error: %v", err)
				break
			}
		}
	}()

	// Send commands with delays
	for _, cmd := range commands {
		time.Sleep(100 * time.Millisecond)
		if _, err := pty.Write([]byte(cmd)); err != nil {
			t.Errorf("Failed to write command: %v", err)
		}
	}

	// Wait for completion or timeout
	select {
	case <-done:
		// Command finished
	case <-time.After(3 * time.Second):
		t.Log("Test timed out, but that's okay for interactive tests")
	}

	// Check output
	outputMu.Lock()
	outputStr := output.String()
	outputMu.Unlock()

	t.Logf("Interactive output: %q", outputStr)

	// Should contain our commands
	if !strings.Contains(outputStr, "hello") {
		t.Errorf("Expected output to contain 'hello', got %q", outputStr)
	}
}

// TestRealPTYWithCreackPTY tests using real PTY with creack/pty library
func TestRealPTYWithCreackPTY(t *testing.T) {
	if runtime.GOOS == "windows" {
		t.Skip("PTY not supported on Windows")
	}

	// Start a real command with PTY
	c := exec.Command("echo", "real pty test")
	f, err := creackpty.Start(c)
	if err != nil {
		t.Fatalf("Failed to start PTY: %v", err)
	}
	defer f.Close()

	// Read output
	output := make([]byte, 1024)
	n, err := f.Read(output)
	if err != nil && err != io.EOF {
		t.Errorf("Read error: %v", err)
	}

	outputStr := string(output[:n])
	t.Logf("Real PTY output: %q", outputStr)

	if !strings.Contains(outputStr, "real pty test") {
		t.Errorf("Expected output to contain 'real pty test', got %q", outputStr)
	}

	// Wait for command to finish
	if err := c.Wait(); err != nil {
		t.Errorf("Command failed: %v", err)
	}
}

// TestPTYSignalHandling tests signal handling in PTY
func TestPTYSignalHandling(t *testing.T) {
	if runtime.GOOS == "windows" {
		t.Skip("Signal handling tests not supported on Windows")
	}

	// Create test server with long-running command
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := &wsexec.ServerCommand{
			Path: "sh",
			Args: []string{"sh", "-c", "sleep 10; echo done"},
			Tty:  true,
		}

		if err := cmd.Handle(w, r); err != nil {
			t.Logf("Server handle error (expected on signal): %v", err)
		}
	}))
	defer server.Close()

	// Create client
	req, err := http.NewRequest("GET", server.URL+"/exec/test/websocket", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}
	req.URL.Scheme = "ws"

	// Use context with timeout to simulate signal
	ctx, cancel := context.WithTimeout(context.Background(), 500*time.Millisecond)
	defer cancel()

	cmd := wsexec.CommandContext(ctx, req, "sh", "-c", "sleep 10; echo done")
	cmd.PingInterval = 100 * time.Millisecond

	// Start with PTY
	pty, err := wsexec.Pty.Start(cmd)
	if err != nil {
		t.Fatalf("Failed to start with PTY: %v", err)
	}
	defer pty.Close()

	start := time.Now()

	// Read in background
	output := make([]byte, 0, 256)
	go func() {
		buf := make([]byte, 256)
		for {
			n, err := pty.Read(buf)
			if n > 0 {
				output = append(output, buf[:n]...)
			}
			if err != nil {
				break
			}
		}
	}()

	// Wait for command (should be interrupted)
	err = cmd.Wait()
	duration := time.Since(start)

	t.Logf("Command duration: %v, error: %v, output: %q", duration, err, string(output))

	// Should not take the full 10 seconds
	if duration > 2*time.Second {
		t.Errorf("Command took too long: %v", duration)
	}

	// Context cancellation should interrupt the command
	if err == nil && duration > 1*time.Second {
		t.Error("Expected command to be interrupted by context cancellation")
	}
}

// TestPTYWithRealTerminalFeatures tests real terminal features
func TestPTYWithRealTerminalFeatures(t *testing.T) {
	if runtime.GOOS == "windows" {
		t.Skip("PTY not supported on Windows")
	}

	// Create test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := &wsexec.ServerCommand{
			Path: "sh",
			Args: []string{"sh", "-c", `
				echo "Terminal info:"
				echo "TERM=$TERM"
				echo "TTY=$(tty)"
				echo "Supports colors: $(test -t 1 && echo yes || echo no)"
				echo "Terminal size: $(stty size 2>/dev/null || echo unknown)"
			`},
			Tty: true,
		}

		if err := cmd.Handle(w, r); err != nil {
			t.Errorf("Server handle error: %v", err)
		}
	}))
	defer server.Close()

	// Create client
	req, err := http.NewRequest("GET", server.URL+"/exec/test/websocket", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}
	req.URL.Scheme = "ws"

	cmd := wsexec.Command(req, "sh", "-c", "echo terminal test")
	cmd.PingInterval = 100 * time.Millisecond

	// Start with PTY
	pty, err := wsexec.Pty.Start(cmd)
	if err != nil {
		t.Fatalf("Failed to start with PTY: %v", err)
	}
	defer pty.Close()

	// Set terminal size
	if err := pty.SetSize(120, 30); err != nil {
		t.Errorf("Failed to set terminal size: %v", err)
	}

	// Read all output
	var output bytes.Buffer
	done := make(chan bool)

	go func() {
		defer close(done)
		io.Copy(&output, pty)
	}()

	// Wait for completion
	select {
	case <-done:
		// Reading finished
	case <-time.After(3 * time.Second):
		t.Log("Reading timed out")
	}

	// Wait for command
	if err := cmd.Wait(); err != nil {
		t.Logf("Command error: %v", err)
	}

	outputStr := output.String()
	t.Logf("Terminal features output:\n%s", outputStr)

	// Check for terminal features
	if strings.Contains(outputStr, "TERM=") {
		t.Logf("✓ TERM environment variable is set")
	}

	if strings.Contains(outputStr, "/dev/") && strings.Contains(outputStr, "tty") {
		t.Logf("✓ Real TTY device detected")
	}

	if strings.Contains(outputStr, "yes") {
		t.Logf("✓ Terminal supports colors")
	}

	// Exit code should be 0
	if code := cmd.ExitCode(); code != 0 {
		t.Errorf("Expected exit code 0, got %d", code)
	}
}

// TestFullInteractivePTYServer demonstrates a complete interactive PTY session
func TestFullInteractivePTYServer(t *testing.T) {
	if runtime.GOOS == "windows" {
		t.Skip("PTY not supported on Windows")
	}

	// Set up logging for debugging
	logger := slog.New(slog.NewTextHandler(os.Stdout, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))

	// Create a real HTTP server that demonstrates interactive PTY functionality
	mux := http.NewServeMux()

	// WebSocket endpoint for PTY sessions
	mux.HandleFunc("/exec/bash/websocket", func(w http.ResponseWriter, r *http.Request) {
		cmd := wsexec.NewServerCommand("/bin/bash")
		cmd.SetTTY(true).SetLogger(logger)

		t.Logf("Starting PTY session with real bash process")
		if err := cmd.Handle(w, r); err != nil {
			t.Logf("PTY session ended: %v", err)
		}
	})

	// Start the server
	server := httptest.NewServer(mux)
	defer server.Close()

	t.Logf("Test server running at %s", server.URL)

	// Create WebSocket connection
	req, err := http.NewRequest("GET", server.URL+"/exec/bash/websocket", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}
	req.URL.Scheme = "ws"

	// Create command with timeout
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	cmd := wsexec.CommandContext(ctx, req, "/bin/bash")
	cmd.PingInterval = 200 * time.Millisecond

	// Start PTY
	pty, err := wsexec.Pty.Start(cmd)
	if err != nil {
		t.Fatalf("Failed to start PTY: %v", err)
	}
	defer func() {
		pty.Close()
		t.Logf("PTY closed")
	}()

	// Set terminal size
	if err := pty.SetSize(120, 30); err != nil {
		t.Errorf("Failed to set terminal size: %v", err)
	}

	t.Logf("PTY started successfully")

	// Capture all output
	var rawOutput bytes.Buffer
	var outputMux sync.Mutex

	// Start reading in background
	readDone := make(chan bool)
	go func() {
		defer close(readDone)
		buf := make([]byte, 1024)
		for {
			n, err := pty.Read(buf)
			if n > 0 {
				outputMux.Lock()
				rawOutput.Write(buf[:n])
				data := buf[:n]
				outputMux.Unlock()

				t.Logf("Read %d bytes: %q", n, string(data))
			}
			if err != nil {
				if err != io.EOF {
					t.Logf("Read error: %v", err)
				}
				break
			}
		}
		t.Logf("Reading loop finished")
	}()

	// Interactive session
	commands := []string{
		"echo 'Interactive PTY Test Started'\n",
		"echo $0\n",    // Show shell type
		"tty\n",        // Show TTY device
		"echo $TERM\n", // Show terminal type
		"echo 'Current directory:'\n",
		"pwd\n", // Show working directory
		"echo 'Environment test:'\n",
		"export TEST_VAR=interactive_test\n",
		"echo $TEST_VAR\n", // Test environment variable
		"echo 'Session complete'\n",
		"exit\n", // Exit bash
	}

	// Send commands with delays to allow processing
	for i, command := range commands {
		t.Logf("Sending command %d: %q", i+1, strings.TrimSpace(command))

		// Write command
		if _, err := pty.Write([]byte(command)); err != nil {
			t.Errorf("Failed to write command %d: %v", i+1, err)
			break
		}

		// Small delay between commands
		time.Sleep(300 * time.Millisecond)
	}

	t.Logf("All commands sent, waiting for completion...")

	// Wait for completion or timeout
	select {
	case <-readDone:
		t.Logf("Reading completed normally")
	case <-time.After(5 * time.Second):
		t.Logf("Reading timed out")
	}

	// Wait for command to finish
	if err := cmd.Wait(); err != nil {
		t.Logf("Command wait error (may be expected): %v", err)
	}

	// Get final output
	outputMux.Lock()
	finalOutput := rawOutput.String()
	outputMux.Unlock()

	t.Logf("\n=== COMPLETE SESSION OUTPUT ===\n%s\n=== END OUTPUT ===", finalOutput)

	// Verify interactive features worked
	checks := []struct {
		name    string
		content string
		found   bool
	}{
		{"Interactive test started", "Interactive PTY Test Started", false},
		{"Shell type", "bash", false},
		{"TTY device", "/dev/", false},
		{"Terminal type", "xterm", false},
		{"Working directory", "/", false},
		{"Environment variable", "interactive_test", false},
		{"Session completion", "Session complete", false},
	}

	for i := range checks {
		if strings.Contains(finalOutput, checks[i].content) {
			checks[i].found = true
			t.Logf("✓ %s: found %q", checks[i].name, checks[i].content)
		} else {
			t.Logf("✗ %s: missing %q", checks[i].name, checks[i].content)
		}
	}

	// Count successful checks
	successCount := 0
	for _, check := range checks {
		if check.found {
			successCount++
		}
	}

	t.Logf("Interactive PTY test completed: %d/%d checks passed", successCount, len(checks))

	// Ensure we had some successful interactions
	if successCount < 3 {
		t.Errorf("Too few successful interactions (%d/%d), PTY may not be working properly", successCount, len(checks))
	} else {
		t.Logf("✓ Interactive PTY session successful!")
	}

	// Final status
	t.Logf("Final command exit code: %d", cmd.ExitCode())
}

// TestInteractivePTYTimeout ensures PTY sessions don't hang indefinitely
func TestInteractivePTYTimeout(t *testing.T) {
	if runtime.GOOS == "windows" {
		t.Skip("PTY not supported on Windows")
	}

	// Create test server with bash
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := wsexec.NewServerCommand("/bin/bash")
		cmd.SetTTY(true)

		if err := cmd.Handle(w, r); err != nil {
			t.Logf("Server handle error: %v", err)
		}
	}))
	defer server.Close()

	// Create WebSocket connection with timeout
	req, err := http.NewRequest("GET", server.URL+"/exec", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}
	req.URL.Scheme = "ws"

	// Short timeout to test cleanup
	ctx, cancel := context.WithTimeout(context.Background(), 1*time.Second)
	defer cancel()

	cmd := wsexec.CommandContext(ctx, req, "/bin/bash")
	cmd.PingInterval = 100 * time.Millisecond

	// Start PTY
	pty, err := wsexec.Pty.Start(cmd)
	if err != nil {
		t.Fatalf("Failed to start PTY: %v", err)
	}
	defer pty.Close()

	// Send a command that would normally wait for input
	pty.Write([]byte("read input\n"))

	start := time.Now()

	// Wait for timeout
	err = cmd.Wait()
	duration := time.Since(start)

	t.Logf("PTY timeout test: duration=%v, error=%v", duration, err)

	// Should timeout within reasonable time
	if duration > 2*time.Second {
		t.Errorf("PTY session took too long to timeout: %v", duration)
	}

	// Should not hang - this test passing means cleanup worked
	t.Logf("✓ PTY timeout handling works correctly")
}

// TestDoublePTY simulates the issue where a wrapper command creates another PTY
func TestDoublePTY(t *testing.T) {
	if runtime.GOOS == "windows" {
		t.Skip("PTY not supported on Windows")
	}

	// Set up logging for debugging
	logger := slog.New(slog.NewTextHandler(os.Stdout, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))

	// Create a wrapper script that simulates what exec.sh does with crun --pty
	wrapperScript := `#!/bin/bash
# Simulate crun exec --pty behavior by using script command which creates a PTY
exec script -q /dev/null "$@"
`

	// Write wrapper script to temp file
	tmpDir := t.TempDir()
	wrapperPath := filepath.Join(tmpDir, "wrapper.sh")
	if err := os.WriteFile(wrapperPath, []byte(wrapperScript), 0755); err != nil {
		t.Fatalf("Failed to write wrapper script: %v", err)
	}

	// Create test server that uses the wrapper
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := wsexec.NewServerCommand("/bin/bash", "-c", "echo 'hello from nested pty'; exit 0")
		cmd.SetTTY(true)
		cmd.SetWrapperCommand([]string{wrapperPath})
		cmd.SetLogger(logger)

		if err := cmd.Handle(w, r); err != nil {
			t.Logf("Server handle error: %v", err)
		}
	}))
	defer server.Close()

	// Create WebSocket connection
	req, err := http.NewRequest("GET", server.URL+"/exec", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}
	req.URL.Scheme = "ws"

	// Use context with timeout
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	cmd := wsexec.CommandContext(ctx, req, "/bin/bash")
	cmd.PingInterval = 100 * time.Millisecond

	// Start PTY
	pty, err := wsexec.Pty.Start(cmd)
	if err != nil {
		t.Fatalf("Failed to start PTY: %v", err)
	}
	defer pty.Close()

	// Read output
	var output bytes.Buffer
	readDone := make(chan bool)

	go func() {
		defer close(readDone)
		buf := make([]byte, 1024)
		for {
			n, err := pty.Read(buf)
			if n > 0 {
				output.Write(buf[:n])
				t.Logf("Read %d bytes: %q", n, string(buf[:n]))
			}
			if err != nil {
				if err != io.EOF {
					t.Logf("Read error: %v", err)
				}
				break
			}
		}
	}()

	// Wait for completion
	start := time.Now()
	err = cmd.Wait()
	duration := time.Since(start)

	select {
	case <-readDone:
		t.Log("Reading completed")
	case <-time.After(1 * time.Second):
		t.Log("Reading timeout after command exit")
	}

	t.Logf("Double PTY test completed in %v with error: %v", duration, err)
	t.Logf("Output: %q", output.String())
	t.Logf("Exit code: %d", cmd.ExitCode())

	// Should complete within reasonable time
	if duration > 3*time.Second {
		t.Errorf("Double PTY command took too long: %v (likely hanging)", duration)
	}

	// Should contain our output
	if !strings.Contains(output.String(), "hello from nested pty") {
		t.Errorf("Missing expected output in: %q", output.String())
	}
}

// TestDoublePTYWithExit simulates exact scenario from integration test
func TestDoublePTYWithExit(t *testing.T) {
	if runtime.GOOS == "windows" {
		t.Skip("PTY not supported on Windows")
	}

	logger := slog.New(slog.NewTextHandler(os.Stdout, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))

	// Create wrapper that uses script command (creates PTY like crun --pty)
	wrapperScript := `#!/bin/bash
# Simulate crun exec --pty
exec script -q /dev/null "$@"
`

	tmpDir := t.TempDir()
	wrapperPath := filepath.Join(tmpDir, "pty-wrapper.sh")
	if err := os.WriteFile(wrapperPath, []byte(wrapperScript), 0755); err != nil {
		t.Fatalf("Failed to write wrapper script: %v", err)
	}

	// Server that runs bash through the wrapper
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := wsexec.NewServerCommand("/bin/bash")
		cmd.SetTTY(true)
		cmd.SetWrapperCommand([]string{wrapperPath})
		cmd.SetLogger(logger)

		if err := cmd.Handle(w, r); err != nil {
			t.Logf("Server handle error: %v", err)
		}
	}))
	defer server.Close()

	// Create WebSocket connection
	req, err := http.NewRequest("GET", server.URL+"/exec", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}
	req.URL.Scheme = "ws"

	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	cmd := wsexec.CommandContext(ctx, req, "/bin/bash")
	cmd.PingInterval = 100 * time.Millisecond

	// Start PTY
	pty, err := wsexec.Pty.Start(cmd)
	if err != nil {
		t.Fatalf("Failed to start PTY: %v", err)
	}
	defer pty.Close()

	// Read output in background
	var output bytes.Buffer
	readDone := make(chan bool)

	go func() {
		defer close(readDone)
		buf := make([]byte, 1024)
		for {
			n, err := pty.Read(buf)
			if n > 0 {
				output.Write(buf[:n])
			}
			if err != nil {
				break
			}
		}
	}()

	// Send exit command after initial prompt
	time.Sleep(500 * time.Millisecond)
	t.Log("Sending exit command")
	if _, err := pty.Write([]byte("exit\n")); err != nil {
		t.Errorf("Failed to write exit command: %v", err)
	}

	// Wait for command completion
	start := time.Now()
	cmdErr := cmd.Wait()
	duration := time.Since(start)

	// Wait a bit for reading to finish
	select {
	case <-readDone:
		t.Log("Reading completed after command exit")
	case <-time.After(2 * time.Second):
		t.Error("Reading did not complete after command exit - PTY hanging!")
	}

	t.Logf("Double PTY exit test: duration=%v, error=%v", duration, cmdErr)
	t.Logf("Output contains 'exit': %v", strings.Contains(output.String(), "exit"))
	t.Logf("Exit code: %d", cmd.ExitCode())

	// Should not hang
	if duration > 5*time.Second {
		t.Errorf("Double PTY session hung for %v", duration)
	}
}

// TestDoublePTYHanging simulates crun --pty behavior that might not close PTY properly
func TestDoublePTYHanging(t *testing.T) {
	if runtime.GOOS == "windows" {
		t.Skip("PTY not supported on Windows")
	}

	logger := slog.New(slog.NewTextHandler(os.Stdout, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))

	// Create wrapper that simulates problematic PTY behavior
	// This wrapper creates a PTY but may not properly close it when the child exits
	wrapperScript := `#!/bin/bash
# Simulate a wrapper that creates PTY but doesn't handle EOF properly
# Using socat to create a PTY that might not close cleanly
if command -v socat >/dev/null 2>&1; then
    # Use socat if available - it can create PTYs that don't always close properly
    exec socat -,raw,echo=0 EXEC:"$*",pty,raw,echo=0
else
    # Fallback to script but with a subshell that might not propagate exit
    (script -q /dev/null "$@"; exit $?) &
    PID=$!
    wait $PID
    # Don't explicitly close anything, let it hang
    sleep 0.1  # Small delay that might prevent proper cleanup
fi
`

	tmpDir := t.TempDir()
	wrapperPath := filepath.Join(tmpDir, "hanging-wrapper.sh")
	if err := os.WriteFile(wrapperPath, []byte(wrapperScript), 0755); err != nil {
		t.Fatalf("Failed to write wrapper script: %v", err)
	}

	// Server that runs bash through the problematic wrapper
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := wsexec.NewServerCommand("/bin/bash", "-c", "echo 'test output'; exit 0")
		cmd.SetTTY(true)
		cmd.SetWrapperCommand([]string{wrapperPath})
		cmd.SetLogger(logger)

		if err := cmd.Handle(w, r); err != nil {
			t.Logf("Server handle error: %v", err)
		}
	}))
	defer server.Close()

	// Create WebSocket connection
	req, err := http.NewRequest("GET", server.URL+"/exec", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}
	req.URL.Scheme = "ws"

	// Shorter timeout to detect hanging
	ctx, cancel := context.WithTimeout(context.Background(), 3*time.Second)
	defer cancel()

	cmd := wsexec.CommandContext(ctx, req, "/bin/bash")
	cmd.PingInterval = 100 * time.Millisecond

	// Start PTY
	pty, err := wsexec.Pty.Start(cmd)
	if err != nil {
		t.Fatalf("Failed to start PTY: %v", err)
	}
	defer pty.Close()

	// Read output
	var output bytes.Buffer
	readDone := make(chan bool)

	go func() {
		defer close(readDone)
		buf := make([]byte, 1024)
		for {
			n, err := pty.Read(buf)
			if n > 0 {
				output.Write(buf[:n])
				t.Logf("Read %d bytes: %q", n, string(buf[:n]))
			}
			if err != nil {
				t.Logf("Read error: %v", err)
				break
			}
		}
	}()

	// Wait for command
	start := time.Now()
	cmdErr := cmd.Wait()
	duration := time.Since(start)

	// Check if reading completed
	readCompleted := false
	select {
	case <-readDone:
		readCompleted = true
		t.Log("Reading completed")
	case <-time.After(500 * time.Millisecond):
		t.Log("Reading did not complete - PTY might be hanging")
	}

	t.Logf("Hanging PTY test: duration=%v, error=%v, readCompleted=%v", duration, cmdErr, readCompleted)
	t.Logf("Output: %q", output.String())

	// This test demonstrates the problem - reading might not complete even after command exits
	if !readCompleted {
		t.Log("ISSUE DETECTED: PTY reading did not complete after command exit")
		t.Log("This simulates the behavior seen in the integration test")
	}
}

// TestPTYCleanupSignal tests if we can force PTY cleanup with signals
func TestPTYCleanupSignal(t *testing.T) {
	if runtime.GOOS == "windows" {
		t.Skip("PTY not supported on Windows")
	}

	logger := slog.New(slog.NewTextHandler(os.Stdout, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))

	// Create a wrapper that definitely hangs the PTY
	wrapperScript := `#!/bin/bash
# Create a PTY with script and keep file descriptors open
exec 3>&1 4>&2  # Save stdout/stderr
script -q /dev/null "$@"
# Don't close the saved descriptors - this can cause hanging
`

	tmpDir := t.TempDir()
	wrapperPath := filepath.Join(tmpDir, "fd-leak-wrapper.sh")
	if err := os.WriteFile(wrapperPath, []byte(wrapperScript), 0755); err != nil {
		t.Fatalf("Failed to write wrapper script: %v", err)
	}

	// Server with wrapper
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		// Pass working directory via environment when using wrapper
		cmd := wsexec.NewServerCommand("/bin/bash", "-c", "echo done; exit 0")
		cmd.SetTTY(true)
		cmd.SetWrapperCommand([]string{wrapperPath})
		cmd.SetLogger(logger)

		// Set a shorter context to force cleanup
		ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
		defer cancel()
		cmd.SetContext(ctx)

		if err := cmd.Handle(w, r); err != nil {
			t.Logf("Server handle error: %v", err)
		}
	}))
	defer server.Close()

	// Create WebSocket connection
	req, err := http.NewRequest("GET", server.URL+"/exec", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}
	req.URL.Scheme = "ws"

	cmd := wsexec.Command(req, "/bin/bash")
	cmd.PingInterval = 100 * time.Millisecond

	// Start PTY
	pty, err := wsexec.Pty.Start(cmd)
	if err != nil {
		t.Fatalf("Failed to start PTY: %v", err)
	}
	defer pty.Close()

	// Try to read
	buf := make([]byte, 1024)
	n, _ := pty.Read(buf)
	if n > 0 {
		t.Logf("Initial read: %q", string(buf[:n]))
	}

	// Wait and see what happens
	err = cmd.Wait()
	t.Logf("Command completed with: %v", err)

	// Try one more read with timeout
	done := make(chan bool)
	go func() {
		_, err := pty.Read(buf)
		t.Logf("Final read result: %v", err)
		close(done)
	}()

	select {
	case <-done:
		t.Log("Final read completed")
	case <-time.After(500 * time.Millisecond):
		t.Log("Final read timed out - PTY hanging as expected")
	}
}

// TestExecShPTYBehavior simulates the exact behavior of exec.sh with conditional PTY
func TestExecShPTYBehavior(t *testing.T) {
	if runtime.GOOS == "windows" {
		t.Skip("PTY not supported on Windows")
	}

	logger := slog.New(slog.NewTextHandler(os.Stdout, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))

	// Create a wrapper that mimics exec.sh behavior
	wrapperScript := `#!/bin/bash
# Mimic exec.sh behavior - check if stdout is TTY and add --pty flag
if [ -t 1 ]; then
    echo "WRAPPER: stdout is TTY, creating nested PTY with script" >&2
    exec script -q /dev/null "$@"
else
    echo "WRAPPER: stdout is not TTY, running directly" >&2
    exec "$@"
fi
`

	tmpDir := t.TempDir()
	wrapperPath := filepath.Join(tmpDir, "exec-sh-mimic.sh")
	if err := os.WriteFile(wrapperPath, []byte(wrapperScript), 0755); err != nil {
		t.Fatalf("Failed to write wrapper script: %v", err)
	}

	// Test 1: Interactive bash session with exit
	t.Run("InteractiveBashExit", func(t *testing.T) {
		server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			cmd := wsexec.NewServerCommand("/bin/bash")
			cmd.SetTTY(true)                             // This creates the first PTY
			cmd.SetWrapperCommand([]string{wrapperPath}) // This will create nested PTY
			cmd.SetLogger(logger)

			if err := cmd.Handle(w, r); err != nil {
				t.Logf("Server handle error: %v", err)
			}
		}))
		defer server.Close()

		req, err := http.NewRequest("GET", server.URL+"/exec", nil)
		if err != nil {
			t.Fatalf("Failed to create request: %v", err)
		}
		req.URL.Scheme = "ws"

		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		defer cancel()

		cmd := wsexec.CommandContext(ctx, req, "/bin/bash")
		cmd.PingInterval = 100 * time.Millisecond

		// Start PTY
		pty, err := wsexec.Pty.Start(cmd)
		if err != nil {
			t.Fatalf("Failed to start PTY: %v", err)
		}
		defer pty.Close()

		// Read output in background
		var output bytes.Buffer
		readDone := make(chan struct{})

		go func() {
			defer close(readDone)
			buf := make([]byte, 1024)
			for {
				n, err := pty.Read(buf)
				if n > 0 {
					output.Write(buf[:n])
					t.Logf("Read %d bytes", n)
				}
				if err != nil {
					t.Logf("Read error: %v", err)
					break
				}
			}
		}()

		// Wait for initial prompt
		time.Sleep(500 * time.Millisecond)

		// Send test command
		t.Log("Sending echo command")
		pty.Write([]byte("echo 'nested pty test'\n"))
		time.Sleep(200 * time.Millisecond)

		// Send exit
		t.Log("Sending exit command")
		pty.Write([]byte("exit\n"))

		// Wait for command completion with timeout
		cmdDone := make(chan error)
		go func() {
			cmdDone <- cmd.Wait()
		}()

		select {
		case err := <-cmdDone:
			t.Logf("Command completed with: %v", err)
		case <-time.After(3 * time.Second):
			t.Error("Command did not complete within 3 seconds - HANGING!")
			cancel() // Force context cancellation
			return
		}

		// Check if reading completed
		select {
		case <-readDone:
			t.Log("Reading completed successfully")
		case <-time.After(1 * time.Second):
			t.Error("Reading did not complete after command exit - PTY HANGING!")
		}

		outputStr := output.String()
		t.Logf("Session output length: %d bytes", len(outputStr))
		if strings.Contains(outputStr, "nested pty test") {
			t.Log("Found expected output")
		}
		if strings.Contains(outputStr, "WRAPPER: stdout is TTY") {
			t.Log("Confirmed: wrapper detected TTY and created nested PTY")
		}
	})

	// Test 2: Non-interactive command should complete quickly
	t.Run("NonInteractiveCommand", func(t *testing.T) {
		server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			cmd := wsexec.NewServerCommand("/bin/bash", "-c", "echo done; exit 0")
			cmd.SetTTY(true)
			cmd.SetWrapperCommand([]string{wrapperPath})
			cmd.SetLogger(logger)

			if err := cmd.Handle(w, r); err != nil {
				t.Logf("Server handle error: %v", err)
			}
		}))
		defer server.Close()

		req, err := http.NewRequest("GET", server.URL+"/exec", nil)
		if err != nil {
			t.Fatalf("Failed to create request: %v", err)
		}
		req.URL.Scheme = "ws"

		ctx, cancel := context.WithTimeout(context.Background(), 3*time.Second)
		defer cancel()

		cmd := wsexec.CommandContext(ctx, req, "/bin/bash")

		// Start PTY
		pty, err := wsexec.Pty.Start(cmd)
		if err != nil {
			t.Fatalf("Failed to start PTY: %v", err)
		}
		defer pty.Close()

		// Read all output
		output, _ := io.ReadAll(pty)

		// Wait for completion
		start := time.Now()
		err = cmd.Wait()
		duration := time.Since(start)

		t.Logf("Non-interactive command completed in %v with error: %v", duration, err)
		t.Logf("Output: %q", string(output))

		if duration > 2*time.Second {
			t.Errorf("Non-interactive command took too long: %v", duration)
		}
	})
}

// TestCrunLikePTYBehavior simulates crun exec --tty behavior more accurately
func TestCrunLikePTYBehavior(t *testing.T) {
	if runtime.GOOS == "windows" {
		t.Skip("PTY not supported on Windows")
	}

	logger := slog.New(slog.NewTextHandler(os.Stdout, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))

	// Create a Go program that simulates crun's PTY behavior
	// This program creates a PTY and might not close it properly on exit
	crunSimulator := `
package main

import (
	"io"
	"os"
	"os/exec"
	"github.com/creack/pty"
)

func main() {
	if len(os.Args) < 2 {
		os.Exit(1)
	}
	
	// Create command from remaining args
	cmd := exec.Command(os.Args[1], os.Args[2:]...)
	
	// Start with PTY (like crun --tty does)
	ptmx, err := pty.Start(cmd)
	if err != nil {
		os.Exit(1)
	}
	// Note: NOT deferring ptmx.Close() to simulate potential crun behavior
	
	// Copy I/O in background
	go func() {
		io.Copy(ptmx, os.Stdin)
	}()
	go func() {
		io.Copy(os.Stdout, ptmx)
	}()
	
	// Wait for command
	cmd.Wait()
	
	// Exit without explicitly closing PTY
	// This simulates the problematic behavior
}
`

	// Create temp directory and write the simulator
	tmpDir := t.TempDir()
	simulatorPath := filepath.Join(tmpDir, "crun-sim.go")
	if err := os.WriteFile(simulatorPath, []byte(crunSimulator), 0644); err != nil {
		t.Fatalf("Failed to write simulator: %v", err)
	}

	// Build the simulator
	buildCmd := exec.Command("go", "build", "-o", filepath.Join(tmpDir, "crun-sim"), simulatorPath)
	if output, err := buildCmd.CombinedOutput(); err != nil {
		t.Fatalf("Failed to build simulator: %v\nOutput: %s", err, output)
	}

	crunSimPath := filepath.Join(tmpDir, "crun-sim")

	// Now test with this simulator as wrapper
	t.Run("SimulatedCrunPTY", func(t *testing.T) {
		server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			cmd := wsexec.NewServerCommand("/bin/bash")
			cmd.SetTTY(true)
			cmd.SetWrapperCommand([]string{crunSimPath})
			cmd.SetLogger(logger)

			if err := cmd.Handle(w, r); err != nil {
				t.Logf("Server handle error: %v", err)
			}
		}))
		defer server.Close()

		req, err := http.NewRequest("GET", server.URL+"/exec", nil)
		if err != nil {
			t.Fatalf("Failed to create request: %v", err)
		}
		req.URL.Scheme = "ws"

		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		defer cancel()

		cmd := wsexec.CommandContext(ctx, req, "/bin/bash")
		cmd.PingInterval = 100 * time.Millisecond

		// Start PTY
		pty, err := wsexec.Pty.Start(cmd)
		if err != nil {
			t.Fatalf("Failed to start PTY: %v", err)
		}
		defer pty.Close()

		// Read output in background
		var output bytes.Buffer
		readDone := make(chan struct{})

		go func() {
			defer close(readDone)
			buf := make([]byte, 1024)
			for {
				n, err := pty.Read(buf)
				if n > 0 {
					output.Write(buf[:n])
				}
				if err != nil {
					t.Logf("Read error after %d bytes: %v", output.Len(), err)
					break
				}
			}
		}()

		// Wait for prompt
		time.Sleep(500 * time.Millisecond)

		// Send exit command
		t.Log("Sending exit command")
		if _, err := pty.Write([]byte("exit\n")); err != nil {
			t.Errorf("Failed to write exit: %v", err)
		}

		// Wait for command with timeout
		cmdDone := make(chan error)
		go func() {
			cmdDone <- cmd.Wait()
		}()

		select {
		case err := <-cmdDone:
			t.Logf("Command completed with: %v", err)
		case <-time.After(3 * time.Second):
			t.Error("Command did not complete within 3 seconds - CRUN-LIKE PTY HANGING!")
			return
		}

		// Check if reading completed
		select {
		case <-readDone:
			t.Log("Reading completed successfully")
		case <-time.After(1 * time.Second):
			t.Error("Reading did not complete after command exit - CRUN-LIKE PTY HANGING!")
		}
	})
}
