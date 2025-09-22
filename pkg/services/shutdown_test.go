package services

import (
	"os"
	"runtime"
	"testing"
	"time"
)

func TestShutdownWithRealProcesses(t *testing.T) {
	// Create temporary directory for test database
	tmpDir, err := os.MkdirTemp("", "services-shutdown-test-*")
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
	services := []struct {
		name  string
		needs []string
	}{
		{"db", []string{}},
		{"api", []string{"db"}},
		{"web", []string{"api"}},
	}

	for _, s := range services {
		svc := &Service{
			Name:  s.name,
			Cmd:   "bash",
			Args:  []string{"-c", "trap 'exit 0' TERM; while true; do sleep 0.1; done"},
			Needs: s.needs,
		}
		if err := manager.CreateService(svc); err != nil {
			t.Fatalf("Failed to create %s: %v", s.name, err)
		}
	}

	// Start the web service (should start all dependencies)
	if err := manager.StartService("web"); err != nil {
		t.Fatal(err)
	}

	// Wait for all to be running
	time.Sleep(100 * time.Millisecond)

	// Verify all are running
	for _, s := range services {
		state, err := manager.GetServiceState(s.name)
		if err != nil {
			t.Fatal(err)
		}
		if state.Status != StatusRunning {
			t.Errorf("Service %s should be running", s.name)
		}
	}

	// Shutdown
	start := time.Now()
	if err := manager.Shutdown(); err != nil {
		t.Fatal(err)
	}
	elapsed := time.Since(start)

	// Should be fast (all graceful)
	if elapsed > 500*time.Millisecond {
		t.Errorf("Shutdown took too long: %v", elapsed)
	}

	// Wait a bit for all process exit events to be processed
	time.Sleep(100 * time.Millisecond)

	// Verify all stopped
	for _, s := range services {
		state, err := manager.GetServiceState(s.name)
		if err != nil {
			t.Fatal(err)
		}
		if state.Status != StatusStopped {
			t.Errorf("Service %s should be stopped after shutdown", s.name)
		}
	}
}

func TestShutdownWithForceKill(t *testing.T) {
	if runtime.GOOS == "darwin" {
		t.Skip("Skipping force kill test on Darwin due to signal handling differences")
	}

	// Create temporary directory for test database
	tmpDir, err := os.MkdirTemp("", "services-forcekill-test-*")
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
	// Create a stubborn service that ignores SIGTERM
	svc := &Service{
		Name: "stubborn",
		Cmd:  "bash",
		Args: []string{"-c", "trap '' TERM; while true; do sleep 0.1; done"},
	}
	if err := manager.CreateService(svc); err != nil {
		t.Fatal(err)
	}

	// Start the service
	if err := manager.StartService("stubborn"); err != nil {
		t.Fatal(err)
	}

	// Wait for it to be running
	time.Sleep(100 * time.Millisecond)

	// Verify it's running
	state, _ := manager.GetServiceState("stubborn")
	if state.Status != StatusRunning {
		t.Fatal("Service should be running")
	}

	// Shutdown - should take about 1 second due to force kill
	start := time.Now()
	if err := manager.Shutdown(); err != nil {
		t.Fatal(err)
	}
	elapsed := time.Since(start)

	// Should take about 1 second (force kill timeout)
	if elapsed < 900*time.Millisecond || elapsed > 1500*time.Millisecond {
		t.Errorf("Expected shutdown to take ~1s (force kill timeout), took %v", elapsed)
	}

	// Verify it's stopped
	state, _ = manager.GetServiceState("stubborn")
	if state.Status != StatusStopped {
		t.Error("Service should be stopped after force kill")
	}
}

func TestShutdownParallelism(t *testing.T) {
	// Create temporary directory for test database
	tmpDir, err := os.MkdirTemp("", "services-parallel-test-*")
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
	// Create independent services that will be stopped in parallel
	serviceNames := []string{"a", "b", "c"}
	for _, name := range serviceNames {
		svc := &Service{
			Name: name,
			Cmd:  "bash",
			Args: []string{"-c", "trap 'sleep 0.2; exit 0' TERM; while true; do sleep 0.1; done"},
		}
		if err := manager.CreateService(svc); err != nil {
			t.Fatal(err)
		}
	}

	// Start all services
	for _, name := range serviceNames {
		if err := manager.StartService(name); err != nil {
			t.Fatal(err)
		}
	}

	// Wait for all to be running
	time.Sleep(100 * time.Millisecond)

	// Shutdown
	start := time.Now()
	if err := manager.Shutdown(); err != nil {
		t.Fatal(err)
	}
	elapsed := time.Since(start)

	// If they were stopped sequentially, it would take 600ms+ (3 * 200ms)
	// If parallel, should be just over 200ms
	if elapsed > 400*time.Millisecond {
		t.Errorf("Shutdown seems sequential, took %v (expected ~200ms for parallel)", elapsed)
	}

	// Wait a bit for all process exit events to be processed
	time.Sleep(100 * time.Millisecond)

	// Verify all stopped
	for _, name := range serviceNames {
		state, _ := manager.GetServiceState(name)
		if state.Status != StatusStopped {
			t.Errorf("Service %s should be stopped", name)
		}
	}
}

func TestShutdownEmptyManager(t *testing.T) {
	// Create temporary directory for test database
	tmpDir, err := os.MkdirTemp("", "services-empty-test-*")
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
	// Start the manager first
	if err := manager.Start(); err != nil {
		t.Fatal(err)
	}

	// Shutdown with no services
	if err := manager.Shutdown(); err != nil {
		t.Fatal(err)
	}
}
