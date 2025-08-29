package container

import (
	"os"
	"strings"
	"testing"
	"time"

	"github.com/superfly/sprite-env/pkg/supervisor"
)

func TestNewProcess(t *testing.T) {
	// Test basic process creation
	config := ProcessConfig{
		Config: supervisor.Config{
			Command: "echo",
			Args:    []string{"hello"},
		},
	}

	process, err := NewProcess(config)
	if err != nil {
		t.Fatalf("Failed to create process: %v", err)
	}
	defer process.Close()

	// Verify supervisor was created
	if process.Supervisor == nil {
		t.Fatal("Supervisor is nil")
	}
}

func TestProcessWithContainersEnabledFromConfig(t *testing.T) {
	// Enable containers for this test
	originalConfig := GetConfig()
	defer Configure(originalConfig)

	Configure(Config{
		Enabled:   true,
		SocketDir: "/tmp/test-containers",
	})

	// Test process creation with containers enabled
	config := ProcessConfig{
		Config: supervisor.Config{
			Command: "echo",
			Args:    []string{"hello"},
		},
	}

	process, err := NewProcess(config)
	if err != nil {
		t.Fatalf("Failed to create process with TTY: %v", err)
	}
	defer process.Stop()

	// Verify TTY was created
	if process.tty == nil {
		t.Fatal("TTY was not created")
	}

	// Check that CONSOLE_SOCKET was added to environment
	foundConsoleSocket := false
	for _, env := range process.config.Env {
		if strings.HasPrefix(env, "CONSOLE_SOCKET=") {
			foundConsoleSocket = true
			break
		}
	}
	if !foundConsoleSocket {
		t.Error("CONSOLE_SOCKET not found in environment")
	}

	// Get TTY path
	ttyPath, err := process.TTYPath()
	if err != nil {
		t.Fatalf("Failed to get TTY path: %v", err)
	}
	if ttyPath == "" {
		t.Error("TTY path is empty")
	}

	// Verify socket file was created
	if _, err := os.Stat(ttyPath); err != nil {
		t.Errorf("Socket file not created at %s: %v", ttyPath, err)
	}
}

func TestProcessWithCustomSocketDir(t *testing.T) {
	// Test with a custom socket directory
	customDir := "/tmp/test-custom-socket-dir"
	os.MkdirAll(customDir, 0755)
	defer os.RemoveAll(customDir)

	// Enable containers with custom directory
	originalConfig := GetConfig()
	defer Configure(originalConfig)

	Configure(Config{
		Enabled:   true,
		SocketDir: customDir,
	})

	config := ProcessConfig{
		Config: supervisor.Config{
			Command: "echo",
			Args:    []string{"hello"},
		},
	}

	process, err := NewProcess(config)
	if err != nil {
		t.Fatalf("Failed to create process with custom TTY path: %v", err)
	}
	defer process.Stop()

	// Verify socket was created in custom directory
	ttyPath, err := process.TTYPath()
	if err != nil {
		t.Fatalf("Failed to get TTY path: %v", err)
	}
	if !strings.HasPrefix(ttyPath, customDir) {
		t.Errorf("Expected TTY path to be in %s, got %s", customDir, ttyPath)
	}

	// Check environment has the socket path
	found := false
	for _, env := range process.config.Env {
		if strings.HasPrefix(env, "CONSOLE_SOCKET=") && strings.Contains(env, customDir) {
			found = true
			break
		}
	}
	if !found {
		t.Errorf("Expected CONSOLE_SOCKET environment variable with path in %s", customDir)
	}
}

func TestProcessBuilder(t *testing.T) {
	// Test the fluent builder interface
	process, err := NewProcessBuilder("sh", "-c", "echo hello").
		WithEnv([]string{"TEST=value"}).
		WithDir("/tmp").
		WithGracePeriod(5 * time.Second).
		WithTTYTimeout(10 * time.Second).
		Build()

	if err != nil {
		t.Fatalf("Failed to build process: %v", err)
	}
	defer process.Stop()

	// Verify configuration
	if process.config.Command != "sh" {
		t.Errorf("Expected command 'sh', got %s", process.config.Command)
	}

	if len(process.config.Args) != 2 || process.config.Args[1] != "echo hello" {
		t.Errorf("Unexpected args: %v", process.config.Args)
	}

	if process.config.Dir != "/tmp" {
		t.Errorf("Expected dir '/tmp', got %s", process.config.Dir)
	}

	if process.config.GracePeriod != 5*time.Second {
		t.Errorf("Expected grace period 5s, got %v", process.config.GracePeriod)
	}

	if process.config.TTYTimeout != 10*time.Second {
		t.Errorf("Expected TTY timeout 10s, got %v", process.config.TTYTimeout)
	}
}

func TestGetTTYWithoutContainers(t *testing.T) {
	// Save original config
	originalConfig := GetConfig()
	defer Configure(originalConfig)

	// Explicitly disable containers
	Configure(Config{
		Enabled:   false,
		SocketDir: "/tmp",
	})

	// Test GetTTY when containers are not enabled
	config := ProcessConfig{
		Config: supervisor.Config{
			Command: "echo",
			Args:    []string{"hello"},
		},
	}

	process, err := NewProcess(config)
	if err != nil {
		t.Fatalf("Failed to create process: %v", err)
	}
	defer process.Close()

	// GetTTY should return error
	_, err = process.GetTTY()
	if err == nil {
		t.Error("Expected error when getting TTY on non-TTY process")
	}

	// TTYPath should return error
	_, err = process.TTYPath()
	if err == nil {
		t.Error("Expected error when getting TTY path on non-TTY process")
	}
}
