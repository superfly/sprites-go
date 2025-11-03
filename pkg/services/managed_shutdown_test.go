package services

import (
	"context"
	"os"
	"sync"
	"testing"
	"time"
)

// Mock managed service that tracks start/stop order
type mockManagedService struct {
	name        string
	startOrder  *[]string
	stopOrder   *[]string
	mu          *sync.Mutex
	startDelay  time.Duration
	stopDelay   time.Duration
	failOnStart bool
	failOnStop  bool
}

func (m *mockManagedService) Start(ctx context.Context, progress ProgressReporter) error {
	if m.startDelay > 0 {
		time.Sleep(m.startDelay)
	}
	progress.ReportProgress("starting " + m.name)

	m.mu.Lock()
	*m.startOrder = append(*m.startOrder, m.name)
	m.mu.Unlock()

	if m.failOnStart {
		return context.DeadlineExceeded
	}

	progress.ReportProgress(m.name + " started")
	return nil
}

func (m *mockManagedService) Stop(ctx context.Context, progress ProgressReporter) error {
	if m.stopDelay > 0 {
		time.Sleep(m.stopDelay)
	}
	progress.ReportProgress("stopping " + m.name)

	m.mu.Lock()
	*m.stopOrder = append(*m.stopOrder, m.name)
	m.mu.Unlock()

	if m.failOnStop {
		return context.DeadlineExceeded
	}

	progress.ReportProgress(m.name + " stopped")
	return nil
}

func (m *mockManagedService) Name() string {
	return m.name
}

// TestManagedServiceShutdownOrder verifies that services are stopped in reverse dependency order
// This replicates the bug where overlay was being stopped before services_manager
func TestManagedServiceShutdownOrder(t *testing.T) {
	tmpDir, err := os.MkdirTemp("", "services-managed-shutdown-test-*")
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

	// Track start and stop order
	var startOrder []string
	var stopOrder []string
	var mu sync.Mutex

	// Create a dependency chain similar to the real system:
	// db_manager -> juicefs -> overlay -> container -> services_manager
	services := []struct {
		name string
		deps []string
	}{
		{"db_manager", []string{}},
		{"juicefs", []string{"db_manager"}},
		{"overlay", []string{"juicefs"}},
		{"container", []string{"overlay"}},
		{"services_manager", []string{"container"}},
	}

	for _, s := range services {
		svcDef := &ServiceDefinition{
			Name:         s.name,
			Dependencies: s.deps,
			ManagedService: &mockManagedService{
				name:       s.name,
				startOrder: &startOrder,
				stopOrder:  &stopOrder,
				mu:         &mu,
			},
		}
		if err := manager.RegisterService(svcDef); err != nil {
			t.Fatalf("Failed to register %s: %v", s.name, err)
		}
	}

	// Start all services
	if err := manager.StartAll(); err != nil {
		t.Fatalf("Failed to start all: %v", err)
	}

	// Verify start order: dependencies before dependents
	expectedStartOrder := []string{"db_manager", "juicefs", "overlay", "container", "services_manager"}
	mu.Lock()
	if len(startOrder) != len(expectedStartOrder) {
		t.Errorf("Expected %d services to start, got %d: %v", len(expectedStartOrder), len(startOrder), startOrder)
	}
	for i, expected := range expectedStartOrder {
		if i >= len(startOrder) {
			break
		}
		if startOrder[i] != expected {
			t.Errorf("Start order mismatch at position %d: expected %s, got %s", i, expected, startOrder[i])
		}
	}
	mu.Unlock()

	// Shutdown all services
	if err := manager.Shutdown(); err != nil {
		t.Fatalf("Failed to shutdown: %v", err)
	}

	// Verify stop order: dependents before dependencies (reverse of start)
	// CRITICAL: services_manager must stop BEFORE overlay (since it has files open on overlay)
	expectedStopOrder := []string{"services_manager", "container", "overlay", "juicefs", "db_manager"}
	mu.Lock()
	if len(stopOrder) != len(expectedStopOrder) {
		t.Errorf("Expected %d services to stop, got %d: %v", len(expectedStopOrder), len(stopOrder), stopOrder)
	}
	for i, expected := range expectedStopOrder {
		if i >= len(stopOrder) {
			break
		}
		if stopOrder[i] != expected {
			t.Errorf("Stop order mismatch at position %d: expected %s, got %s (full order: %v)",
				i, expected, stopOrder[i], stopOrder)
		}
	}
	mu.Unlock()
}

// TestManagedServiceParallelStartup verifies services at same level start in parallel
func TestManagedServiceParallelStartup(t *testing.T) {
	tmpDir, err := os.MkdirTemp("", "services-parallel-start-test-*")
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

	var startOrder []string
	var stopOrder []string
	var mu sync.Mutex

	// Create services at same dependency level (no dependencies)
	// Each takes 100ms to start
	for _, name := range []string{"svc1", "svc2", "svc3"} {
		svcDef := &ServiceDefinition{
			Name:         name,
			Dependencies: []string{},
			ManagedService: &mockManagedService{
				name:       name,
				startOrder: &startOrder,
				stopOrder:  &stopOrder,
				mu:         &mu,
				startDelay: 100 * time.Millisecond,
			},
		}
		if err := manager.RegisterService(svcDef); err != nil {
			t.Fatalf("Failed to register %s: %v", name, err)
		}
	}

	// Start all services - should be parallel
	start := time.Now()
	if err := manager.StartAll(); err != nil {
		t.Fatalf("Failed to start all: %v", err)
	}
	elapsed := time.Since(start)

	// If parallel, should take ~100ms (all start at once)
	// If sequential, would take ~300ms (100ms * 3)
	if elapsed > 200*time.Millisecond {
		t.Errorf("Startup appears sequential, took %v (expected ~100ms for parallel)", elapsed)
	}

	// All 3 should have started
	mu.Lock()
	if len(startOrder) != 3 {
		t.Errorf("Expected 3 services to start, got %d", len(startOrder))
	}
	mu.Unlock()

	// Cleanup
	if err := manager.Shutdown(); err != nil {
		t.Fatalf("Failed to shutdown: %v", err)
	}
}

// TestManagedServiceStopTree verifies StopServiceTree stops a service and its dependents
func TestManagedServiceStopTree(t *testing.T) {
	tmpDir, err := os.MkdirTemp("", "services-stop-tree-test-*")
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

	var startOrder []string
	var stopOrder []string
	var mu sync.Mutex

	// Create a dependency tree: base -> middle -> top
	services := []struct {
		name string
		deps []string
	}{
		{"base", []string{}},
		{"middle", []string{"base"}},
		{"top", []string{"middle"}},
	}

	for _, s := range services {
		svcDef := &ServiceDefinition{
			Name:         s.name,
			Dependencies: s.deps,
			ManagedService: &mockManagedService{
				name:       s.name,
				startOrder: &startOrder,
				stopOrder:  &stopOrder,
				mu:         &mu,
			},
		}
		if err := manager.RegisterService(svcDef); err != nil {
			t.Fatalf("Failed to register %s: %v", s.name, err)
		}
	}

	// Start all services
	if err := manager.StartAll(); err != nil {
		t.Fatalf("Failed to start all: %v", err)
	}

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

	// Stop the middle service and everything that depends on it
	// This should stop: top, middle (in that order)
	// base should remain running
	if err := manager.StopServiceTree("middle"); err != nil {
		t.Fatalf("Failed to stop service tree: %v", err)
	}

	// Wait a bit
	time.Sleep(100 * time.Millisecond)

	// Verify stop order
	mu.Lock()
	expectedStops := []string{"top", "middle"}
	if len(stopOrder) != len(expectedStops) {
		t.Errorf("Expected %d services to stop, got %d: %v", len(expectedStops), len(stopOrder), stopOrder)
	}
	for i, expected := range expectedStops {
		if i >= len(stopOrder) {
			break
		}
		if stopOrder[i] != expected {
			t.Errorf("Stop order mismatch at position %d: expected %s, got %s", i, expected, stopOrder[i])
		}
	}
	mu.Unlock()

	// Verify base is still running
	state, err := manager.GetServiceState("base")
	if err != nil {
		t.Fatal(err)
	}
	if state.Status != StatusRunning {
		t.Error("Service base should still be running")
	}

	// Verify middle and top are stopped
	for _, name := range []string{"middle", "top"} {
		state, err := manager.GetServiceState(name)
		if err != nil {
			t.Fatal(err)
		}
		if state.Status != StatusStopped {
			t.Errorf("Service %s should be stopped", name)
		}
	}

	// Cleanup
	if err := manager.Shutdown(); err != nil {
		t.Fatalf("Failed to shutdown: %v", err)
	}
}
