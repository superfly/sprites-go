package services

import (
	"os"
	"testing"
	"time"
)

func TestSignalService(t *testing.T) {
	// Create temporary directory for test database
	tmpDir, err := os.MkdirTemp("", "services-signal-test-*")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(tmpDir)

	manager, err := NewManager(tmpDir)
	if err != nil {
		t.Fatal(err)
	}
	defer manager.Close()

	// Start the manager
	if err := manager.Start(); err != nil {
		t.Fatal(err)
	}
	// Create a service that ignores SIGTERM
	svc := &Service{
		Name: "signal-test",
		Cmd:  "bash",
		Args: []string{"-c", "trap 'echo ignoring SIGTERM' TERM; while true; do sleep 0.1; done"},
	}
	if err := manager.CreateService(svc); err != nil {
		t.Fatal(err)
	}

	// Start the service
	if err := manager.StartService("signal-test"); err != nil {
		t.Fatal(err)
	}

	// Wait for it to be running
	time.Sleep(100 * time.Millisecond)

	// Send SIGTERM (should be ignored)
	if err := manager.SignalService("signal-test", "TERM"); err != nil {
		t.Fatal(err)
	}

	// Wait a bit and verify it's still running
	time.Sleep(200 * time.Millisecond)
	state, _ := manager.GetServiceState("signal-test")
	if state.Status != StatusRunning {
		t.Error("Service should still be running after SIGTERM")
	}

	// Send SIGKILL (cannot be ignored)
	if err := manager.SignalService("signal-test", "KILL"); err != nil {
		t.Fatal(err)
	}

	// Wait for stop
	if err := manager.WaitForStop("signal-test", 2*time.Second); err != nil {
		t.Fatal("Service should have stopped after SIGKILL")
	}

	// Verify it's stopped
	state, _ = manager.GetServiceState("signal-test")
	if state.Status != StatusStopped {
		t.Error("Service should be stopped after SIGKILL")
	}
}

func TestSignalNonRunningService(t *testing.T) {
	// Create temporary directory for test database
	tmpDir, err := os.MkdirTemp("", "services-signal-test-*")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(tmpDir)

	manager, err := NewManager(tmpDir)
	if err != nil {
		t.Fatal(err)
	}
	defer manager.Close()

	// Start the manager
	if err := manager.Start(); err != nil {
		t.Fatal(err)
	}
	// Create a service that exits immediately
	svc := &Service{
		Name: "quick-exit",
		Cmd:  "echo",
		Args: []string{"done"},
	}
	if err := manager.CreateService(svc); err != nil {
		t.Fatal(err)
	}

	// Start the service
	if err := manager.StartService("quick-exit"); err != nil {
		t.Fatal(err)
	}

	// Wait for it to exit
	time.Sleep(100 * time.Millisecond)

	// Try to signal it - should fail
	err = manager.SignalService("quick-exit", "TERM")
	if err == nil {
		t.Error("Expected error signaling non-running service")
	}
	if err != nil && !contains(err.Error(), "not running") {
		t.Errorf("Expected 'not running' error, got: %v", err)
	}
}

func TestSignalInvalidSignal(t *testing.T) {
	// Create temporary directory for test database
	tmpDir, err := os.MkdirTemp("", "services-signal-test-*")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(tmpDir)

	manager, err := NewManager(tmpDir)
	if err != nil {
		t.Fatal(err)
	}
	defer manager.Close()

	// Start the manager
	if err := manager.Start(); err != nil {
		t.Fatal(err)
	}
	// Create a long-running service
	svc := &Service{
		Name: "test-service",
		Cmd:  "sleep",
		Args: []string{"10"},
	}
	if err := manager.CreateService(svc); err != nil {
		t.Fatal(err)
	}

	// Start the service
	if err := manager.StartService("test-service"); err != nil {
		t.Fatal(err)
	}

	// Wait for it to be running
	time.Sleep(100 * time.Millisecond)

	// Send invalid signal
	err = manager.SignalService("test-service", "INVALID")
	if err == nil {
		t.Error("Expected error for invalid signal")
	}
	if err != nil && !contains(err.Error(), "unknown signal") {
		t.Errorf("Expected 'unknown signal' error, got: %v", err)
	}
}

func contains(s, substr string) bool {
	return len(s) >= len(substr) && s[len(s)-len(substr):] == substr ||
		len(s) >= len(substr) && s[:len(substr)] == substr ||
		len(s) > len(substr) && findSubstring(s, substr)
}

func findSubstring(s, substr string) bool {
	for i := 0; i <= len(s)-len(substr); i++ {
		if s[i:i+len(substr)] == substr {
			return true
		}
	}
	return false
}
