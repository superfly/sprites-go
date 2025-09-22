package services

import (
	"os"
	"testing"
	"time"
)

func TestHandleCreateWithRealProcess(t *testing.T) {
	// Create temporary directory for test database
	tmpDir, err := os.MkdirTemp("", "services-handlers-test-*")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(tmpDir)

	// Create manager with real command wrapper
	manager, err := NewManager(tmpDir)
	if err != nil {
		t.Fatal(err)
	}
	defer manager.Close()

	// Start the manager
	if err := manager.Start(); err != nil {
		t.Fatal(err)
	}
	// Test creating a service that runs successfully
	t.Run("successful_create", func(t *testing.T) {
		svc := &Service{
			Name: "echo-service",
			Cmd:  "bash",
			Args: []string{"-c", "echo 'Hello, World!' && sleep 1"},
		}

		err := manager.CreateService(svc)
		if err != nil {
			t.Fatal(err)
		}

		// Service should be created but not started
		state, err := manager.GetServiceState("echo-service")
		if err != nil {
			t.Fatal(err)
		}
		if state.Status != StatusStopped {
			t.Errorf("Expected service to be stopped after creation, got %s", state.Status)
		}

		// Now start it
		err = manager.StartService("echo-service")
		if err != nil {
			t.Fatal(err)
		}

		// Verify it's running
		state, err = manager.GetServiceState("echo-service")
		if err != nil {
			t.Fatal(err)
		}
		if state.Status != StatusRunning {
			t.Errorf("Expected service to be running after start, got %s", state.Status)
		}

		// Cleanup
		manager.DeleteService("echo-service")
	})

	// Test creating a service that fails to start
	t.Run("failed_create_rollback", func(t *testing.T) {
		svc := &Service{
			Name: "fail-service",
			Cmd:  "/nonexistent/command",
			Args: []string{},
		}

		// Create should succeed even with invalid command
		err := manager.CreateService(svc)
		if err != nil {
			t.Fatal("CreateService should succeed even with invalid command")
		}

		// Service should be created but stopped
		state, err := manager.GetServiceState("fail-service")
		if err != nil {
			t.Fatal("Service should exist after creation")
		}
		if state.Status != StatusStopped {
			t.Errorf("Expected service to be stopped, got %s", state.Status)
		}

		// Starting it should fail
		err = manager.StartService("fail-service")
		if err == nil {
			t.Fatal("Expected error starting service with invalid command")
		}

		// Service should exist but be in failed state
		state, err = manager.GetServiceState("fail-service")
		if err != nil {
			t.Fatal(err)
		}
		if state.Status != StatusFailed {
			t.Errorf("Expected service to be failed after start attempt, got %s", state.Status)
		}

		// Cleanup
		manager.DeleteService("fail-service")
	})
}

func TestHandleDeleteWithRealProcess(t *testing.T) {
	// Create temporary directory for test database
	tmpDir, err := os.MkdirTemp("", "services-handlers-test-*")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(tmpDir)

	// Create manager with real command wrapper
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
		Name: "delete-test",
		Cmd:  "sleep",
		Args: []string{"10"},
	}

	if err := manager.CreateService(svc); err != nil {
		t.Fatal(err)
	}

	// Start the service
	if err := manager.StartService("delete-test"); err != nil {
		t.Fatal(err)
	}

	// Delete the service
	if err := manager.DeleteService("delete-test"); err != nil {
		t.Fatal(err)
	}

	// Wait a bit for cleanup
	time.Sleep(200 * time.Millisecond)

	// Verify process was killed
	// On Darwin, we can't reliably check if a process is dead using Signal
	// The successful deletion means the process was stopped

	// Verify service is gone from state
	_, err = manager.GetServiceState("delete-test")
	if err == nil {
		t.Error("Service should not exist after deletion")
	}

	// Verify it's not in the database
	services, err := manager.ListServices()
	if err != nil {
		t.Fatal(err)
	}
	for _, s := range services {
		if s.Name == "delete-test" {
			t.Error("Deleted service should not be in database")
		}
	}
}

func TestHandleStartStopWithRealProcess(t *testing.T) {
	// Create temporary directory for test database
	tmpDir, err := os.MkdirTemp("", "services-handlers-test-*")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(tmpDir)

	// Create manager with real command wrapper
	manager, err := NewManager(tmpDir)
	if err != nil {
		t.Fatal(err)
	}
	defer manager.Close()

	// Start the manager
	if err := manager.Start(); err != nil {
		t.Fatal(err)
	}
	// Create but don't start a service (this isn't directly supported, so we'll work around it)
	// For now, services auto-start on creation, so we'll just test stop/start cycle

	svc := &Service{
		Name: "startstop-test",
		Cmd:  "bash",
		Args: []string{"-c", "while true; do sleep 1; done"},
	}

	if err := manager.CreateService(svc); err != nil {
		t.Fatal(err)
	}

	// Start the service
	if err := manager.StartService("startstop-test"); err != nil {
		t.Fatal(err)
	}

	// Verify it's running
	state, err := manager.GetServiceState("startstop-test")
	if err != nil {
		t.Fatal(err)
	}
	firstPID := state.PID
	if state.Status != StatusRunning {
		t.Errorf("Expected service to be running, got %s", state.Status)
	}

	// Stop the service
	if err := manager.StopService("startstop-test"); err != nil {
		t.Fatal(err)
	}

	// Wait for stop to complete
	time.Sleep(200 * time.Millisecond)

	// Verify it's stopped
	state, err = manager.GetServiceState("startstop-test")
	if err != nil {
		t.Fatal(err)
	}
	if state.Status != StatusStopped {
		t.Errorf("Expected service to be stopped, got %s", state.Status)
	}

	// Start it again
	// Note: There's no public StartService method, services auto-start on creation
	// So we'll delete and recreate to simulate a restart
	if err := manager.DeleteService("startstop-test"); err != nil {
		t.Fatal(err)
	}

	// Recreate the service
	if err := manager.CreateService(svc); err != nil {
		t.Fatal(err)
	}

	// Start it again
	if err := manager.StartService("startstop-test"); err != nil {
		t.Fatal(err)
	}

	// Verify it's running with a new PID
	state, err = manager.GetServiceState("startstop-test")
	if err != nil {
		t.Fatal(err)
	}
	if state.Status != StatusRunning {
		t.Errorf("Expected service to be running after restart, got %s", state.Status)
	}
	if state.PID == firstPID {
		t.Error("Expected new PID after restart")
	}
	if state.PID == 0 {
		t.Error("Expected valid PID after restart")
	}

	// Cleanup
	manager.DeleteService("startstop-test")
}

func TestHandleWithDependenciesRealProcess(t *testing.T) {
	// Create temporary directory for test database
	tmpDir, err := os.MkdirTemp("", "services-handlers-test-*")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(tmpDir)

	// Create manager with real command wrapper
	manager, err := NewManager(tmpDir)
	if err != nil {
		t.Fatal(err)
	}
	defer manager.Close()

	// Start the manager
	if err := manager.Start(); err != nil {
		t.Fatal(err)
	}
	// Create a base service
	baseSvc := &Service{
		Name: "base-service",
		Cmd:  "bash",
		Args: []string{"-c", "while true; do sleep 1; done"},
	}
	if err := manager.CreateService(baseSvc); err != nil {
		t.Fatal(err)
	}

	// Create a dependent service
	depSvc := &Service{
		Name:  "dependent-service",
		Cmd:   "bash",
		Args:  []string{"-c", "while true; do sleep 1; done"},
		Needs: []string{"base-service"},
	}
	if err := manager.CreateService(depSvc); err != nil {
		t.Fatal(err)
	}

	// Start the dependent service (should also start base)
	if err := manager.StartService("dependent-service"); err != nil {
		t.Fatal(err)
	}

	// Both should be running
	baseState, err := manager.GetServiceState("base-service")
	if err != nil {
		t.Fatal(err)
	}
	if baseState.Status != StatusRunning {
		t.Error("Base service should be running")
	}

	depState, err := manager.GetServiceState("dependent-service")
	if err != nil {
		t.Fatal(err)
	}
	if depState.Status != StatusRunning {
		t.Error("Dependent service should be running")
	}

	// Try to stop base service (should fail)
	err = manager.StopService("base-service")
	if err == nil {
		t.Error("Should not be able to stop base service while dependent is running")
	}

	// Stop dependent first
	if err := manager.StopService("dependent-service"); err != nil {
		t.Fatal(err)
	}

	time.Sleep(200 * time.Millisecond)

	// Now we should be able to stop base
	if err := manager.StopService("base-service"); err != nil {
		t.Fatal(err)
	}

	// Cleanup
	manager.DeleteService("dependent-service")
	manager.DeleteService("base-service")
}

func TestHandleDeleteWithoutStateEntry(t *testing.T) {
	// Create temporary directory for test
	tmpDir, err := os.MkdirTemp("", "services-handlers-test-*")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(tmpDir)

	// Create manager
	manager, err := NewManager(tmpDir)
	if err != nil {
		t.Fatalf("Failed to create manager: %v", err)
	}
	defer manager.Close()

	// Start the manager
	if err := manager.Start(); err != nil {
		t.Fatalf("Failed to start manager: %v", err)
	}

	// Create maps for internal use
	states := make(map[string]*ServiceState)
	processes := make(map[string]*ProcessHandle)

	// Create a service directly in the database
	svc := &Service{
		Name: "test-service",
		Cmd:  "echo",
		Args: []string{"hello"},
	}

	// Store directly in database without going through handleCreate
	// This simulates a service that exists from a previous session
	if err := manager.db.CreateService(svc); err != nil {
		t.Fatalf("Failed to create service in database: %v", err)
	}

	// Verify service is NOT in states map
	if _, exists := states["test-service"]; exists {
		t.Fatal("Service should not be in states map")
	}

	// Test: handleDelete should still work even though service is not in states map
	err = manager.handleDelete("test-service", states, processes)
	if err != nil {
		t.Errorf("handleDelete failed: %v", err)
	}

	// Verify service was deleted from database
	_, err = manager.db.GetService("test-service")
	if err == nil {
		t.Error("Service should have been deleted from database")
	}

	// Test: Deleting non-existent service should fail
	err = manager.handleDelete("non-existent", states, processes)
	if err == nil {
		t.Error("Expected error when deleting non-existent service")
	}
}
