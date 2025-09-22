package services

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

func TestDependencyValidation(t *testing.T) {
	// Create temporary directory for test database
	tmpDir, err := os.MkdirTemp("", "services-test-*")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(tmpDir)

	// Use real command wrapper for testing
	manager, err := NewManager(tmpDir)
	if err != nil {
		t.Fatal(err)
	}
	defer manager.Close()

	// Start the manager
	if err := manager.Start(); err != nil {
		t.Fatal(err)
	}
	// Test 1: Create service with no dependencies
	svc1 := &Service{
		Name:  "service1",
		Cmd:   "sleep",
		Args:  []string{"10"},
		Needs: []string{},
	}
	if err := manager.CreateService(svc1); err != nil {
		t.Errorf("Failed to create service with no dependencies: %v", err)
	}

	// Test 2: Create service with valid dependency
	svc2 := &Service{
		Name:  "service2",
		Cmd:   "sleep",
		Args:  []string{"10"},
		Needs: []string{"service1"},
	}
	if err := manager.CreateService(svc2); err != nil {
		t.Errorf("Failed to create service with valid dependency: %v", err)
	}

	// Test 3: Create service with non-existent dependency
	svc3 := &Service{
		Name:  "service3",
		Cmd:   "/bin/echo",
		Args:  []string{"test"},
		Needs: []string{"nonexistent"},
	}
	if err := manager.CreateService(svc3); err == nil {
		t.Error("Expected error for non-existent dependency, got nil")
	}

	// Test 4: Test that self-dependency is caught
	svc4 := &Service{
		Name:  "service4",
		Cmd:   "/bin/echo",
		Args:  []string{"self"},
		Needs: []string{"service4"}, // Self dependency
	}
	if err := manager.CreateService(svc4); err == nil {
		t.Error("Expected error for self dependency, got nil")
	}

	// Note: Testing true circular dependencies would require the ability to update
	// existing services' dependencies, which we don't currently support.
	// For a true circular dependency test, we would need:
	// 1. Create A depending on B
	// 2. Create B with no dependencies
	// 3. Update B to depend on A (creating A->B->A cycle)
}

func TestServiceCRUD(t *testing.T) {
	// Create temporary directory for test database
	tmpDir, err := os.MkdirTemp("", "services-test-*")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(tmpDir)

	// Use real command wrapper for testing
	manager, err := NewManager(tmpDir)
	if err != nil {
		t.Fatal(err)
	}
	defer manager.Close()

	// Start the manager
	if err := manager.Start(); err != nil {
		t.Fatal(err)
	}
	// Create a service
	svc := &Service{
		Name:  "test-service",
		Cmd:   "sleep",
		Args:  []string{"10"},
		Needs: []string{},
	}

	// Test Create
	if err := manager.CreateService(svc); err != nil {
		t.Fatalf("Failed to create service: %v", err)
	}

	// Test Get
	retrieved, err := manager.GetService("test-service")
	if err != nil {
		t.Fatalf("Failed to get service: %v", err)
	}
	if retrieved.Name != svc.Name || retrieved.Cmd != svc.Cmd {
		t.Error("Retrieved service doesn't match created service")
	}

	// Test List
	services, err := manager.ListServices()
	if err != nil {
		t.Fatalf("Failed to list services: %v", err)
	}
	if len(services) != 1 {
		t.Errorf("Expected 1 service, got %d", len(services))
	}

	// Test Delete
	if err := manager.DeleteService("test-service"); err != nil {
		t.Fatalf("Failed to delete service: %v", err)
	}

	// Verify deletion
	services, err = manager.ListServices()
	if err != nil {
		t.Fatalf("Failed to list services after deletion: %v", err)
	}
	if len(services) != 0 {
		t.Errorf("Expected 0 services after deletion, got %d", len(services))
	}
}

func TestServiceState(t *testing.T) {
	// Create temporary directory for test database
	tmpDir, err := os.MkdirTemp("", "services-test-*")
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
	// Create a service
	svc := &Service{
		Name:  "state-test",
		Cmd:   "/bin/echo",
		Args:  []string{"state"},
		Needs: []string{},
	}

	if err := manager.CreateService(svc); err != nil {
		t.Fatalf("Failed to create service: %v", err)
	}

	// Get state - should be stopped after creation
	state, err := manager.GetServiceState("state-test")
	if err != nil {
		t.Fatalf("Failed to get service state: %v", err)
	}
	if state.Status != StatusStopped {
		t.Errorf("Expected status to be stopped after creation, got %s", state.Status)
	}

	// Start the service
	if err := manager.StartService("state-test"); err != nil {
		t.Fatal(err)
	}

	// Now it should be running
	state, err = manager.GetServiceState("state-test")
	if err != nil {
		t.Fatal(err)
	}
	if state.Status != StatusRunning {
		t.Errorf("Expected status to be running after start, got %s", state.Status)
	}
	if state.PID <= 0 {
		t.Errorf("Expected valid PID (> 0), got %d", state.PID)
	}

	// Wait a bit for the mock process to "exit"
	time.Sleep(15 * time.Millisecond)

	// Check state again - should be stopped now
	state, err = manager.GetServiceState("state-test")
	if err != nil {
		t.Fatalf("Failed to get service state after exit: %v", err)
	}
	if state.Status != StatusStopped {
		t.Errorf("Expected status to be stopped after process exit, got %s", state.Status)
	}
}

func TestServiceStartFailure(t *testing.T) {
	// Create temporary directory for test database
	tmpDir, err := os.MkdirTemp("", "services-test-*")
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
	// Try to create a service - should fail
	svc := &Service{
		Name:  "fail-service",
		Cmd:   "/nonexistent/command",
		Args:  []string{"--help"},
		Needs: []string{},
	}

	// Create should succeed even with invalid command
	err = manager.CreateService(svc)
	if err != nil {
		t.Errorf("CreateService should succeed even with invalid command, got: %v", err)
	}

	// Service should be created
	_, err = manager.GetService("fail-service")
	if err != nil {
		t.Error("Service should exist in database after creation")
	}

	// Starting it should fail
	err = manager.StartService("fail-service")
	if err == nil {
		t.Error("Expected error when starting service with invalid command, got nil")
	}
	if !strings.Contains(err.Error(), "failed to start") {
		t.Errorf("Expected error message to contain 'failed to start', got: %v", err)
	}

	// Service should still be in database but in failed state
	state, err := manager.GetServiceState("fail-service")
	if err != nil {
		t.Error("Service should exist in database after failed start")
	}
	if state.Status != StatusFailed {
		t.Errorf("Expected service to be in failed state, got %s", state.Status)
	}
}

func TestStopWithDependencies(t *testing.T) {
	// Create temporary directory for test database
	tmpDir, err := os.MkdirTemp("", "services-test-*")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(tmpDir)

	// Use real command wrapper for testing
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
		Name:  "database",
		Cmd:   "sleep",
		Args:  []string{"10"},
		Needs: []string{},
	}
	if err := manager.CreateService(baseSvc); err != nil {
		t.Fatalf("Failed to create base service: %v", err)
	}

	// Create a dependent service
	depSvc := &Service{
		Name:  "webapp",
		Cmd:   "sleep",
		Args:  []string{"10"},
		Needs: []string{"database"},
	}
	if err := manager.CreateService(depSvc); err != nil {
		t.Fatalf("Failed to create dependent service: %v", err)
	}

	// Start the dependent service (should also start database)
	if err := manager.StartService("webapp"); err != nil {
		t.Fatal(err)
	}

	// Both should be running
	dbState, _ := manager.GetServiceState("database")
	if dbState.Status != StatusRunning {
		t.Error("Database should be running")
	}
	webState, _ := manager.GetServiceState("webapp")
	if webState.Status != StatusRunning {
		t.Error("Webapp should be running")
	}

	// Try to stop database - should fail because webapp depends on it
	err = manager.StopService("database")
	if err == nil {
		t.Error("Expected error when stopping service with running dependents")
	}
	if !strings.Contains(err.Error(), "webapp depends on it") {
		t.Errorf("Expected error about webapp dependency, got: %v", err)
	}

	// Database should still be running
	dbState, _ = manager.GetServiceState("database")
	if dbState.Status != StatusRunning {
		t.Error("Database should still be running after failed stop")
	}

	// Stop webapp first
	if err := manager.StopService("webapp"); err != nil {
		t.Errorf("Failed to stop webapp: %v", err)
	}

	// Now stopping database should succeed
	if err := manager.StopService("database"); err != nil {
		t.Errorf("Failed to stop database after dependent stopped: %v", err)
	}
}

func TestShutdown(t *testing.T) {
	// Create temporary directory for test database
	tmpDir, err := os.MkdirTemp("", "services-test-*")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(tmpDir)

	manager, err := NewManager(tmpDir)
	if err != nil {
		t.Fatal(err)
	}
	// Don't use defer Close since we're testing Shutdown

	// Start the manager
	if err := manager.Start(); err != nil {
		t.Fatal(err)
	}

	// Create a service hierarchy:
	// db (no deps)
	// cache (no deps)
	// api (needs: db, cache)
	// webapp (needs: api)

	services := []struct {
		name  string
		needs []string
	}{
		{"db", []string{}},
		{"cache", []string{}},
		{"api", []string{"db", "cache"}},
		{"webapp", []string{"api"}},
	}

	for _, s := range services {
		svc := &Service{
			Name:  s.name,
			Cmd:   "sleep",
			Args:  []string{"10"},
			Needs: s.needs,
		}
		if err := manager.CreateService(svc); err != nil {
			t.Fatalf("Failed to create service %s: %v", s.name, err)
		}
	}

	// Start webapp (which should start all dependencies)
	if err := manager.StartService("webapp"); err != nil {
		t.Fatal(err)
	}

	// All should be running
	for _, s := range services {
		state, _ := manager.GetServiceState(s.name)
		if state.Status != StatusRunning {
			t.Errorf("Service %s should be running", s.name)
		}
	}

	// Shutdown
	if err := manager.Shutdown(); err != nil {
		t.Fatalf("Shutdown failed: %v", err)
	}

	// Wait a bit for shutdown to complete
	time.Sleep(50 * time.Millisecond)

	// Verify all services are stopped
	for _, s := range services {
		state, _ := manager.GetServiceState(s.name)
		if state.Status != StatusStopped {
			t.Errorf("Service %s should be stopped after shutdown", s.name)
		}
	}

	// Close the manager
	manager.db.Close()
}

func indexOf(slice []string, item string) int {
	for i, v := range slice {
		if v == item {
			return i
		}
	}
	return -1
}

func TestDBOperations(t *testing.T) {
	// Create temporary directory for test database
	tmpDir, err := os.MkdirTemp("", "services-test-*")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(tmpDir)

	// Create database
	db, err := NewDB(tmpDir)
	if err != nil {
		t.Fatal(err)
	}
	defer db.Close()

	// Test service with array fields
	svc := &Service{
		Name:  "db-test",
		Cmd:   "/bin/sh",
		Args:  []string{"-c", "echo hello"},
		Needs: []string{"dep1", "dep2"},
	}

	// Create
	if err := db.CreateService(svc); err != nil {
		t.Fatalf("Failed to create service in DB: %v", err)
	}

	// Get
	retrieved, err := db.GetService("db-test")
	if err != nil {
		t.Fatalf("Failed to get service from DB: %v", err)
	}

	// Verify arrays are properly stored and retrieved
	if len(retrieved.Args) != 2 || retrieved.Args[0] != "-c" || retrieved.Args[1] != "echo hello" {
		t.Error("Args not properly stored/retrieved")
	}
	if len(retrieved.Needs) != 2 || retrieved.Needs[0] != "dep1" || retrieved.Needs[1] != "dep2" {
		t.Error("Needs not properly stored/retrieved")
	}

	// Test that DB file exists
	dbPath := filepath.Join(tmpDir, "services.db")
	if _, err := os.Stat(dbPath); os.IsNotExist(err) {
		t.Error("Database file was not created")
	}
}
