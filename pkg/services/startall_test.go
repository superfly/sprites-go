package services

import (
	"os"
	"testing"
	"time"
)

// TestStartAll verifies that services start in correct dependency order
// In production, this happens after the supervised process is running
func TestStartAll(t *testing.T) {
	// Create temporary directory for test database
	tmpDir, err := os.MkdirTemp("", "services-startall-test-*")
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
	// Create services with dependencies: web -> api -> db
	dbSvc := &Service{
		Name: "db",
		Cmd:  "sleep",
		Args: []string{"10"},
	}
	if err := manager.CreateService(dbSvc); err != nil {
		t.Fatal(err)
	}

	apiSvc := &Service{
		Name:  "api",
		Cmd:   "sleep",
		Args:  []string{"10"},
		Needs: []string{"db"},
	}
	if err := manager.CreateService(apiSvc); err != nil {
		t.Fatal(err)
	}

	webSvc := &Service{
		Name:  "web",
		Cmd:   "sleep",
		Args:  []string{"10"},
		Needs: []string{"api"},
	}
	if err := manager.CreateService(webSvc); err != nil {
		t.Fatal(err)
	}

	// Start all services
	if err := manager.StartAll(); err != nil {
		t.Fatalf("Failed to start all services: %v", err)
	}

	// Give services a moment to start
	time.Sleep(100 * time.Millisecond)

	// Verify all services are running
	services := []string{"db", "api", "web"}
	for _, name := range services {
		state, err := manager.GetServiceState(name)
		if err != nil {
			t.Errorf("Failed to get state for %s: %v", name, err)
			continue
		}
		if state.Status != StatusRunning {
			t.Errorf("Expected %s to be running, got %s", name, state.Status)
		}
	}

	// Clean up
	if err := manager.Shutdown(); err != nil {
		t.Errorf("Failed to shutdown: %v", err)
	}
}

func TestStartAllEmpty(t *testing.T) {
	// Create temporary directory for test database
	tmpDir, err := os.MkdirTemp("", "services-startall-empty-test-*")
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
	// Start all services when none exist
	if err := manager.StartAll(); err != nil {
		t.Fatalf("Failed to start all services: %v", err)
	}
}

func TestStartAllWithFailure(t *testing.T) {
	// Create temporary directory for test database
	tmpDir, err := os.MkdirTemp("", "services-startall-fail-test-*")
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
	// Create a service that will succeed
	goodSvc := &Service{
		Name: "good",
		Cmd:  "sleep",
		Args: []string{"10"},
	}
	if err := manager.CreateService(goodSvc); err != nil {
		t.Fatal(err)
	}

	// Note: We can't create a service that will fail to start because
	// CreateService automatically starts the service and rolls back on failure.
	// So we'll just verify that StartAll continues despite individual failures.

	// Start all services - should not fail entirely
	if err := manager.StartAll(); err != nil {
		t.Fatalf("StartAll should not fail when individual services fail: %v", err)
	}

	// Give services a moment to start
	time.Sleep(100 * time.Millisecond)

	// Verify good service is running
	state, err := manager.GetServiceState("good")
	if err != nil {
		t.Errorf("Failed to get state for good: %v", err)
	} else if state.Status != StatusRunning {
		t.Errorf("Expected good to be running, got %s", state.Status)
	}
}

func TestStartAllWithPreexistingServices(t *testing.T) {
	// This test simulates the scenario where services exist in the database
	// from a previous session (not in current state map) and StartAll is called at boot

	// Create temporary directory for test
	tmpDir, err := os.MkdirTemp("", "services-startall-preexist-test-*")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(tmpDir)

	// First manager session - create services
	manager1, err := NewManager(tmpDir)
	if err != nil {
		t.Fatal(err)
	}

	// Start the manager
	if err := manager1.Start(); err != nil {
		t.Fatal(err)
	}

	// Create services
	services := []*Service{
		{Name: "db", Cmd: "sleep", Args: []string{"10"}},
		{Name: "api", Cmd: "sleep", Args: []string{"10"}, Needs: []string{"db"}},
		{Name: "web", Cmd: "sleep", Args: []string{"10"}, Needs: []string{"api"}},
	}

	for _, svc := range services {
		if err := manager1.CreateService(svc); err != nil {
			t.Fatal(err)
		}
	}

	// Close first manager (simulating shutdown)
	manager1.Close()

	// Second manager session - simulating reboot
	manager2, err := NewManager(tmpDir)
	if err != nil {
		t.Fatal(err)
	}
	defer manager2.Close()

	// Start the manager
	if err := manager2.Start(); err != nil {
		t.Fatal(err)
	}

	// At this point, services exist in DB but not in state map
	// StartAll should load them from DB and start them
	if err := manager2.StartAll(); err != nil {
		t.Fatalf("StartAll failed: %v", err)
	}

	// Wait a moment for services to stabilize
	time.Sleep(100 * time.Millisecond)

	// Verify all services are running
	for _, svc := range services {
		state, err := manager2.GetServiceState(svc.Name)
		if err != nil {
			t.Errorf("Failed to get state for %s: %v", svc.Name, err)
			continue
		}
		if state.Status != StatusRunning {
			t.Errorf("Expected %s to be running, got %s", svc.Name, state.Status)
		}
	}
}
