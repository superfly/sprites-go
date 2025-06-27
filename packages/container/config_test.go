package container

import (
	"os"
	"strings"
	"testing"
	"time"

	"github.com/sprite-env/packages/supervisor"
)

func TestConfigure(t *testing.T) {
	// Save original config
	originalConfig := GetConfig()
	defer Configure(originalConfig)

	// Test default configuration
	defaultCfg := DefaultConfig()
	if defaultCfg.Enabled {
		t.Error("Default config should have containers disabled")
	}
	if defaultCfg.SocketDir != "/tmp" {
		t.Errorf("Default socket dir should be /tmp, got %s", defaultCfg.SocketDir)
	}

	// Configure with custom settings
	Configure(Config{
		Enabled:   true,
		SocketDir: "/var/run/containers",
	})

	// Verify configuration was applied
	if !IsEnabled() {
		t.Error("Containers should be enabled")
	}
	if GetSocketDir() != "/var/run/containers" {
		t.Errorf("Socket dir should be /var/run/containers, got %s", GetSocketDir())
	}

	// Test with empty socket dir (should default to /tmp)
	Configure(Config{
		Enabled:   true,
		SocketDir: "",
	})

	if GetSocketDir() != "/tmp" {
		t.Errorf("Empty socket dir should default to /tmp, got %s", GetSocketDir())
	}
}

func TestProcessWithContainersDisabled(t *testing.T) {
	// Save original config
	originalConfig := GetConfig()
	defer Configure(originalConfig)

	// Explicitly disable containers
	Configure(Config{
		Enabled:   false,
		SocketDir: "/tmp",
	})

	// Create a process
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

	// Verify no TTY was created
	if process.tty != nil {
		t.Error("TTY should not be created when containers are disabled")
	}

	// Verify CONSOLE_SOCKET is not in environment
	for _, env := range process.config.Env {
		if strings.HasPrefix(env, "CONSOLE_SOCKET=") {
			t.Error("CONSOLE_SOCKET should not be set when containers are disabled")
		}
		if env == "CONTAINER_WRAPPED=true" {
			t.Error("CONTAINER_WRAPPED should not be set when containers are disabled")
		}
	}

	// TTYPath should return error
	_, err = process.TTYPath()
	if err == nil {
		t.Error("TTYPath should return error when containers are disabled")
	}

	// GetTTY should return error
	_, err = process.GetTTY()
	if err == nil {
		t.Error("GetTTY should return error when containers are disabled")
	}
}

func TestProcessWithContainersEnabled(t *testing.T) {
	// Save original config
	originalConfig := GetConfig()
	defer Configure(originalConfig)

	// Enable containers
	Configure(Config{
		Enabled:   true,
		SocketDir: "/tmp/test-enabled",
	})

	// Create directory
	os.MkdirAll("/tmp/test-enabled", 0755)
	defer os.RemoveAll("/tmp/test-enabled")

	// Create a container process (using crun command to trigger container detection)
	config := ProcessConfig{
		Config: supervisor.Config{
			Command: "crun",
			Args:    []string{"exec", "testcontainer", "echo", "hello"},
		},
		TTYTimeout: 3 * time.Second,
	}

	process, err := NewProcess(config)
	if err != nil {
		t.Fatalf("Failed to create process: %v", err)
	}
	defer process.Stop()

	// Verify TTY was created
	if process.tty == nil {
		t.Fatal("TTY should be created when containers are enabled")
	}

	// Verify socket path is in the configured directory
	ttyPath, err := process.TTYPath()
	if err != nil {
		t.Fatalf("Failed to get TTY path: %v", err)
	}
	if !strings.HasPrefix(ttyPath, "/tmp/test-enabled/") {
		t.Errorf("TTY path should be in /tmp/test-enabled/, got %s", ttyPath)
	}

	// Verify environment variables are set
	hasConsoleSocket := false
	hasContainerWrapped := false

	for _, env := range process.config.Env {
		if strings.HasPrefix(env, "CONSOLE_SOCKET=") {
			hasConsoleSocket = true
			if !strings.Contains(env, "/tmp/test-enabled/") {
				t.Errorf("CONSOLE_SOCKET should point to socket in /tmp/test-enabled/, got %s", env)
			}
		}
		if env == "CONTAINER_WRAPPED=true" {
			hasContainerWrapped = true
		}
	}

	if !hasConsoleSocket {
		t.Error("CONSOLE_SOCKET environment variable not set")
	}
	if !hasContainerWrapped {
		t.Error("CONTAINER_WRAPPED environment variable not set")
	}
}

func TestConfigureCreatesDirectory(t *testing.T) {
	// Save original config
	originalConfig := GetConfig()
	defer Configure(originalConfig)

	// Use a test directory that doesn't exist
	testDir := "/tmp/test-container-sockets-" + strings.ReplaceAll(time.Now().Format(time.RFC3339Nano), ":", "-")
	defer os.RemoveAll(testDir)

	// Verify directory doesn't exist
	if _, err := os.Stat(testDir); !os.IsNotExist(err) {
		t.Fatal("Test directory already exists")
	}

	// Configure with the non-existent directory
	Configure(Config{
		Enabled:   true,
		SocketDir: testDir,
	})

	// Verify directory was created
	if _, err := os.Stat(testDir); err != nil {
		t.Errorf("Directory should have been created: %v", err)
	}
}
