package wsexec_test

import (
	"bytes"
	"net/http"
	"net/http/httptest"
	"runtime"
	"strings"
	"testing"
	"time"

	"github.com/sprite-env/packages/wsexec"
)

// TestPTYBasicEcho tests basic PTY functionality with echo
func TestPTYBasicEcho(t *testing.T) {
	// Create test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := &wsexec.ServerCommand{
			Path: "sh",
			Args: []string{"sh", "-c", "echo $TERM"},
			Tty:  true,
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

	var stdout bytes.Buffer
	cmd := wsexec.Command(req, "sh", "-c", "echo $TERM")
	cmd.Stdout = &stdout
	cmd.Tty = true
	cmd.PingInterval = 100 * time.Millisecond

	// Add a small timeout to wait for any output
	done := make(chan error, 1)
	go func() {
		done <- cmd.Run()
	}()

	select {
	case err := <-done:
		if err != nil {
			t.Fatalf("Command failed: %v", err)
		}
	case <-time.After(2 * time.Second):
		t.Fatal("Command timed out")
	}

	// With TTY, $TERM should be set to xterm
	output := strings.TrimSpace(stdout.String())
	if !strings.HasPrefix(output, "xterm") {
		t.Errorf("Expected output to start with 'xterm', got %q", output)
	}
}

// TestPTYDebug tests basic PTY functionality with more debugging
func TestPTYDebug(t *testing.T) {
	// Create test server that echoes a simple message
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := &wsexec.ServerCommand{
			Path: "echo",
			Args: []string{"echo", "TTY_TEST_OUTPUT"},
			Tty:  true,
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

	var stdout, stderr bytes.Buffer
	// Note: client Args are ignored since server hard-codes the command
	cmd := wsexec.Command(req, "echo", "ignored")
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr
	cmd.Tty = true
	cmd.PingInterval = 100 * time.Millisecond

	// Run with timeout
	done := make(chan error, 1)
	go func() {
		done <- cmd.Run()
	}()

	select {
	case err := <-done:
		if err != nil {
			t.Fatalf("Command failed: %v", err)
		}
	case <-time.After(2 * time.Second):
		t.Fatal("Command timed out")
	}

	// Debug output
	t.Logf("Stdout: %q", stdout.String())
	t.Logf("Stderr: %q", stderr.String())
	t.Logf("Exit code: %d", cmd.ExitCode())

	// With TTY, should have the output
	output := stdout.String()
	if !strings.Contains(output, "TTY_TEST_OUTPUT") {
		t.Errorf("Expected output to contain 'TTY_TEST_OUTPUT', got %q", output)
	}
}

// TestTTYvsNonTTY compares TTY and non-TTY execution to isolate the issue
func TestTTYvsNonTTY(t *testing.T) {
	testCases := []struct {
		name string
		tty  bool
	}{
		{"NonTTY", false},
		{"TTY", true},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			// Create test server
			server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
				cmd := &wsexec.ServerCommand{
					Path: "echo",
					Args: []string{"echo", "TEST_OUTPUT"},
					Tty:  tc.tty,
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

			var stdout, stderr bytes.Buffer
			cmd := wsexec.Command(req, "echo", "TEST_OUTPUT")
			cmd.Stdout = &stdout
			cmd.Stderr = &stderr
			cmd.Tty = tc.tty
			cmd.PingInterval = 100 * time.Millisecond

			// Run the command
			err = cmd.Run()

			t.Logf("TTY=%v: err=%v, stdout=%q, stderr=%q, exitCode=%d",
				tc.tty, err, stdout.String(), stderr.String(), cmd.ExitCode())

			if err != nil {
				t.Fatalf("Command failed: %v", err)
			}

			// Both modes should produce output
			if !strings.Contains(stdout.String(), "TEST_OUTPUT") {
				t.Errorf("Expected stdout to contain 'TEST_OUTPUT', got %q", stdout.String())
			}

			// Exit code should be 0
			if code := cmd.ExitCode(); code != 0 {
				t.Errorf("Expected exit code 0, got %d", code)
			}
		})
	}
}

// TestPTYWindowResize tests PTY window resize functionality
func TestPTYWindowResize(t *testing.T) {
	if runtime.GOOS == "windows" {
		t.Skip("PTY not supported on Windows")
	}

	// Create test server that checks terminal size
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := &wsexec.ServerCommand{
			Path: "stty",
			Args: []string{"stty", "size"},
			Tty:  true,
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

	cmd := wsexec.Command(req, "stty", "size")
	cmd.Tty = true
	cmd.PingInterval = 100 * time.Millisecond

	// Start with PTY
	pty, err := wsexec.Pty.Start(cmd)
	if err != nil {
		t.Fatalf("Failed to start with PTY: %v", err)
	}
	defer pty.Close()

	// Set size
	if err := pty.SetSize(80, 24); err != nil {
		t.Errorf("Failed to set size: %v", err)
	}

	// Wait a bit then read output
	time.Sleep(200 * time.Millisecond)

	// Read output
	output := make([]byte, 256)
	n, err := pty.Read(output)
	if err != nil && n == 0 {
		t.Logf("No output from stty size command")
	}

	outputStr := string(output[:n])
	t.Logf("PTY size output: %q", outputStr)

	// Wait for command to finish
	if err := cmd.Wait(); err != nil {
		t.Logf("Wait error: %v", err)
	}
}

// TestPTYWithEnvironmentVariables tests PTY with custom environment variables
func TestPTYWithEnvironmentVariables(t *testing.T) {
	// Create test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := &wsexec.ServerCommand{
			Path: "sh",
			Args: []string{"sh", "-c", "echo $CUSTOM_VAR"},
			Env:  []string{"CUSTOM_VAR=test_value"},
			Tty:  true,
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

	var stdout bytes.Buffer
	cmd := wsexec.Command(req, "sh", "-c", "echo $CUSTOM_VAR")
	cmd.Stdout = &stdout
	cmd.Tty = true
	cmd.PingInterval = 100 * time.Millisecond

	if err := cmd.Run(); err != nil {
		t.Fatalf("Command failed: %v", err)
	}

	// Check output
	output := strings.TrimSpace(stdout.String())
	if output != "test_value" {
		t.Errorf("Expected 'test_value', got %q", output)
	}
}
