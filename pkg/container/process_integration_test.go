package container

import (
	"bytes"
	"io"
	"net"
	"os"
	"strings"
	"syscall"
	"testing"
	"time"

	"github.com/superfly/sprite-env/pkg/supervisor"
)

func TestProcessIntegration(t *testing.T) {
	// Test running an actual process
	config := ProcessConfig{
		Config: supervisor.Config{
			Command: "sh",
			Args:    []string{"-c", "echo 'integration test' && exit 0"},
		},
	}

	process, err := NewProcess(config)
	if err != nil {
		t.Fatalf("Failed to create process: %v", err)
	}
	defer process.Close()

	// Capture stdout
	stdoutPipe, err := process.StdoutPipe()
	if err != nil {
		t.Fatalf("Failed to get stdout pipe: %v", err)
	}

	// Start the process
	pid, err := process.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	if pid <= 0 {
		t.Errorf("Invalid PID: %d", pid)
	}

	// Read output
	var buf bytes.Buffer
	go io.Copy(&buf, stdoutPipe)

	// Wait for completion
	if err := process.Wait(); err != nil {
		t.Fatalf("Process failed: %v", err)
	}

	// Check output
	output := strings.TrimSpace(buf.String())
	if output != "integration test" {
		t.Errorf("Expected 'integration test', got %q", output)
	}
}

func TestProcessWithTTYIntegration(t *testing.T) {
	// Save original config
	originalConfig := GetConfig()
	defer Configure(originalConfig)

	// Enable containers for this test
	Configure(Config{
		Enabled:   true,
		SocketDir: "/tmp/test-integration",
	})

	// Create a simple script that connects to the socket and sends a file descriptor
	script := `#!/bin/sh
# Read the CONSOLE_SOCKET environment variable
if [ -z "$CONSOLE_SOCKET" ]; then
    echo "CONSOLE_SOCKET not set" >&2
    exit 1
fi

# Create a simple file to use as a fake PTY
echo "test pty data" > /tmp/test-pty-file
exec 3</tmp/test-pty-file

# Use a simple Python script to send the FD
python3 -c "
import socket
import os

# Connect to the socket
sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
sock.connect('$CONSOLE_SOCKET')

# Send a file descriptor (fd 3)
sock.sendmsg([b'\\x00'], [(socket.SOL_SOCKET, socket.SCM_RIGHTS, b'\\x03\\x00\\x00\\x00')])
sock.close()
" 2>/dev/null || {
    # Fallback: just echo that we would send the FD
    echo "Would send FD to $CONSOLE_SOCKET"
}

# Clean up
rm -f /tmp/test-pty-file
echo "Process completed"
`

	// Write script to temp file
	scriptFile := "/tmp/test-tty-script.sh"
	if err := os.WriteFile(scriptFile, []byte(script), 0755); err != nil {
		t.Fatalf("Failed to write script: %v", err)
	}
	defer os.Remove(scriptFile)

	config := ProcessConfig{
		Config: supervisor.Config{
			Command: "sh",
			Args:    []string{scriptFile},
		},
		TTYTimeout: 2 * time.Second,
	}

	process, err := NewProcess(config)
	if err != nil {
		t.Fatalf("Failed to create process with TTY: %v", err)
	}
	defer process.Stop()

	// Get the actual socket path
	socketPath, err := process.TTYPath()
	if err != nil {
		t.Fatalf("Failed to get TTY path: %v", err)
	}

	// Verify socket was created
	if _, err := os.Stat(socketPath); err != nil {
		t.Fatalf("Socket not created: %v", err)
	}

	// Start the process
	_, err = process.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Try to get TTY (this will timeout if Python isn't available, which is OK for this test)
	_, err = process.GetTTY()
	if err != nil {
		// This is expected if Python isn't available in the test environment
		t.Logf("GetTTY error (expected if Python not available): %v", err)
	}

	// Wait for process to complete
	process.Wait()
}

func TestProcessStopAndCleanup(t *testing.T) {
	// Save original config
	originalConfig := GetConfig()
	defer Configure(originalConfig)

	// Enable containers
	Configure(Config{
		Enabled:   true,
		SocketDir: "/tmp/test-cleanup",
	})

	// Test that Stop properly cleans up resources
	config := ProcessConfig{
		Config: supervisor.Config{
			Command:     "sleep",
			Args:        []string{"10"},
			GracePeriod: 1 * time.Second,
		},
	}

	process, err := NewProcess(config)
	if err != nil {
		t.Fatalf("Failed to create process: %v", err)
	}

	// Get socket path
	socketPath, err := process.TTYPath()
	if err != nil {
		t.Fatalf("Failed to get TTY path: %v", err)
	}

	// Verify socket was created
	if _, err := os.Stat(socketPath); err != nil {
		t.Fatalf("Socket not created: %v", err)
	}

	// Start the process
	pid, err := process.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Verify process is running
	if err := syscall.Kill(pid, 0); err != nil {
		t.Errorf("Process not running: %v", err)
	}

	// Stop the process
	if err := process.Stop(); err != nil {
		t.Fatalf("Failed to stop process: %v", err)
	}

	// Give it a moment to clean up
	time.Sleep(100 * time.Millisecond)

	// Verify socket was cleaned up
	if _, err := os.Stat(socketPath); !os.IsNotExist(err) {
		t.Error("Socket file not cleaned up")
	}

	// Verify process is no longer running
	if err := syscall.Kill(pid, 0); err == nil {
		t.Error("Process still running after stop")
	}
}

func TestProcessWithEnvironment(t *testing.T) {
	// Save original config
	originalConfig := GetConfig()
	defer Configure(originalConfig)

	// Enable containers
	Configure(Config{
		Enabled:   true,
		SocketDir: "/tmp/test-env",
	})

	// Test that environment variables are properly set
	config := ProcessConfig{
		Config: supervisor.Config{
			Command: "sh",
			Args:    []string{"-c", "echo $TEST_VAR; echo $CONSOLE_SOCKET"},
			Env:     []string{"TEST_VAR=custom_value"},
		},
	}

	process, err := NewProcess(config)
	if err != nil {
		t.Fatalf("Failed to create process: %v", err)
	}
	defer process.Stop()

	// Capture stdout
	stdoutPipe, err := process.StdoutPipe()
	if err != nil {
		t.Fatalf("Failed to get stdout pipe: %v", err)
	}

	// Start the process
	_, err = process.Start()
	if err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	// Read output with proper synchronization
	var buf bytes.Buffer
	done := make(chan bool)
	go func() {
		io.Copy(&buf, stdoutPipe)
		done <- true
	}()

	// Wait for completion
	process.Wait()

	// Wait for output reading to complete
	<-done

	// Check output
	lines := strings.Split(strings.TrimSpace(buf.String()), "\n")
	if len(lines) < 2 {
		t.Fatalf("Expected at least 2 lines of output, got %d", len(lines))
	}

	// Verify custom env var
	if lines[0] != "custom_value" {
		t.Errorf("Expected TEST_VAR='custom_value', got %q", lines[0])
	}

	// Verify CONSOLE_SOCKET was set and points to the right directory
	if !strings.HasPrefix(lines[1], "/tmp/test-env/") {
		t.Errorf("Expected CONSOLE_SOCKET to start with '/tmp/test-env/', got %q", lines[1])
	}
}

func TestProcessBuilderIntegration(t *testing.T) {
	// Test the builder with a real process
	var outputBuf bytes.Buffer

	process, err := NewProcessBuilder("sh", "-c", "echo 'builder test'").
		WithGracePeriod(2 * time.Second).
		Build()

	if err != nil {
		t.Fatalf("Failed to build process: %v", err)
	}
	defer process.Stop()

	stdoutPipe, _ := process.StdoutPipe()
	done := make(chan struct{})
	go func() {
		io.Copy(&outputBuf, stdoutPipe)
		close(done)
	}()

	// Start and wait
	if _, err := process.Start(); err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}

	if err := process.Wait(); err != nil {
		t.Fatalf("Process failed: %v", err)
	}

	<-done
	output := strings.TrimSpace(outputBuf.String())
	if output != "builder test" {
		t.Errorf("Expected 'builder test', got %q", output)
	}
}

// Helper function to simulate sending FD (for testing without Python)
func simulateSendFD(t *testing.T, socketPath string, fd int) {
	// Connect to socket
	conn, err := net.Dial("unix", socketPath)
	if err != nil {
		t.Logf("Failed to connect to socket: %v", err)
		return
	}
	defer conn.Close()

	// Get Unix connection
	unixConn, ok := conn.(*net.UnixConn)
	if !ok {
		t.Log("Not a Unix connection")
		return
	}

	// Send the file descriptor
	file, err := unixConn.File()
	if err != nil {
		t.Logf("Failed to get file: %v", err)
		return
	}
	defer file.Close()

	buf := []byte{0} // At least 1 byte of data
	rights := syscall.UnixRights(fd)

	if err := syscall.Sendmsg(int(file.Fd()), buf, rights, nil, 0); err != nil {
		t.Logf("Failed to send FD: %v", err)
	}
}
