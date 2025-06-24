package wsexec_test

import (
	"bytes"
	"context"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
	"time"

	"github.com/sprite-env/packages/wsexec"
)

// TestNewServerInterface tests the new server interface API
func TestNewServerInterface(t *testing.T) {
	t.Run("NewServerCommand", func(t *testing.T) {
		cmd := wsexec.NewServerCommand("echo", "hello")

		if cmd.Path != "echo" {
			t.Errorf("Expected path 'echo', got %q", cmd.Path)
		}
		if len(cmd.Args) != 2 || cmd.Args[0] != "echo" || cmd.Args[1] != "hello" {
			t.Errorf("Expected args ['echo', 'hello'], got %v", cmd.Args)
		}
	})

	t.Run("NewServerCommandContext", func(t *testing.T) {
		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		defer cancel()

		cmd := wsexec.NewServerCommandContext(ctx, "echo", "hello")

		if cmd.GetContext() != ctx {
			t.Error("Expected context to be set")
		}
	})

	t.Run("SetterMethods", func(t *testing.T) {
		cmd := wsexec.NewServerCommand("echo", "hello")

		// Test chaining
		cmd.SetTTY(true).
			SetEnv([]string{"FOO=bar"}).
			SetWorkingDir("/tmp").
			SetWrapperCommand([]string{"sudo"})

		if !cmd.Tty {
			t.Error("Expected TTY to be true")
		}
		if len(cmd.Env) != 1 || cmd.Env[0] != "FOO=bar" {
			t.Errorf("Expected env ['FOO=bar'], got %v", cmd.Env)
		}
		if cmd.Dir != "/tmp" {
			t.Errorf("Expected dir '/tmp', got %q", cmd.Dir)
		}
		if len(cmd.WrapperCommand) != 1 || cmd.WrapperCommand[0] != "sudo" {
			t.Errorf("Expected wrapper ['sudo'], got %v", cmd.WrapperCommand)
		}
	})
}

// TestServerCommandWithEnvironment tests environment variable handling
func TestServerCommandWithEnvironment(t *testing.T) {
	// Create test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := wsexec.NewServerCommand("sh", "-c", "echo $TEST_VAR")
		cmd.SetEnv([]string{"TEST_VAR=hello_from_env"})

		if err := cmd.Handle(w, r); err != nil {
			t.Errorf("Server handle error: %v", err)
		}
	}))
	defer server.Close()

	// Create client
	req, err := http.NewRequest("GET", server.URL+"/exec", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}
	req.URL.Scheme = "ws"

	var stdout bytes.Buffer
	cmd := wsexec.Command(req, "sh", "-c", "echo $TEST_VAR")
	cmd.Stdout = &stdout

	if err := cmd.Run(); err != nil {
		t.Fatalf("Command failed: %v", err)
	}

	// Check output
	output := strings.TrimSpace(stdout.String())
	if output != "hello_from_env" {
		t.Errorf("Expected 'hello_from_env', got %q", output)
	}
}

// TestServerCommandWithWorkingDirectory tests working directory handling
func TestServerCommandWithWorkingDirectory(t *testing.T) {
	// Create test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := wsexec.NewServerCommand("pwd")
		cmd.SetWorkingDir("/tmp")

		if err := cmd.Handle(w, r); err != nil {
			t.Errorf("Server handle error: %v", err)
		}
	}))
	defer server.Close()

	// Create client
	req, err := http.NewRequest("GET", server.URL+"/exec", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}
	req.URL.Scheme = "ws"

	var stdout bytes.Buffer
	cmd := wsexec.Command(req, "pwd")
	cmd.Stdout = &stdout

	if err := cmd.Run(); err != nil {
		t.Fatalf("Command failed: %v", err)
	}

	// Check output
	output := strings.TrimSpace(stdout.String())
	if output != "/tmp" && output != "/private/tmp" {
		t.Errorf("Expected '/tmp' or '/private/tmp', got %q", output)
	}
}

// TestServerCommandContextCancellation tests context cancellation in server commands
func TestServerCommandContextCancellation(t *testing.T) {
	// Create context with timeout
	ctx, cancel := context.WithTimeout(context.Background(), 200*time.Millisecond)
	defer cancel()

	// Create test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := wsexec.NewServerCommandContext(ctx, "sleep", "10")

		// This should be cancelled by context timeout
		if err := cmd.Handle(w, r); err != nil {
			t.Logf("Server handle error (expected): %v", err)
		}
	}))
	defer server.Close()

	// Create client
	req, err := http.NewRequest("GET", server.URL+"/exec", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}
	req.URL.Scheme = "ws"

	cmd := wsexec.Command(req, "sleep", "10")

	start := time.Now()
	err = cmd.Run()
	duration := time.Since(start)

	// The command might succeed or fail depending on timing, but should be quick
	if duration > 1*time.Second {
		t.Errorf("Command took too long: %v", duration)
	}
}
