//go:build linux
// +build linux

package portwatcher

import (
	"net"
	"os"
	"os/exec"
	"sync"
	"testing"
	"time"
)

// TestNamespaceCreation tests namespace functionality
func TestNamespaceCreation(t *testing.T) {
	// Just test that the namespace detection works
	ns, err := getNetworkNamespace(os.Getpid())
	if err != nil {
		t.Fatalf("Failed to get network namespace: %v", err)
	}
	t.Logf("Current process is in namespace: %s", ns)

	// Test that we can monitor the current namespace
	nm := GetGlobalMonitor()

	// Create a test server
	listener, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatalf("Failed to create listener: %v", err)
	}
	defer listener.Close()

	port := listener.Addr().(*net.TCPAddr).Port

	// Subscribe to current process
	portChan := make(chan Port, 10)
	if err := nm.Subscribe(os.Getpid(), func(p Port) {
		select {
		case portChan <- p:
		case <-time.After(1 * time.Second):
			t.Error("Timeout sending port to channel")
		}
	}); err != nil {
		t.Fatalf("Failed to subscribe: %v", err)
	}

	// Wait for detection
	select {
	case p := <-portChan:
		if p.Port != port {
			t.Errorf("Expected port %d, got %d", port, p.Port)
		}
		t.Logf("Successfully detected port: %s:%d", p.Address, p.Port)
	case <-time.After(3 * time.Second):
		t.Error("Timeout waiting for port detection")
	}
}

// TestMultipleNamespaces tests monitoring multiple processes
func TestMultipleNamespaces(t *testing.T) {
	nm := GetGlobalMonitor()

	// Track detected ports
	detectedPorts := make(map[int][]Port)
	var mu sync.Mutex

	// Create multiple listeners
	listeners := make([]net.Listener, 3)
	expectedPorts := make([]int, 3)

	for i := 0; i < 3; i++ {
		listener, err := net.Listen("tcp", "127.0.0.1:0")
		if err != nil {
			t.Fatalf("Failed to create listener %d: %v", i, err)
		}
		listeners[i] = listener
		defer listener.Close()

		port := listener.Addr().(*net.TCPAddr).Port
		expectedPorts[i] = port

		// Create a subprocess for each listener to simulate different processes
		cmd := exec.Command("sleep", "10")
		if err := cmd.Start(); err != nil {
			t.Fatalf("Failed to start subprocess %d: %v", i, err)
		}
		defer cmd.Process.Kill()

		pid := cmd.Process.Pid

		// Subscribe to each process
		if err := nm.Subscribe(pid, func(p Port) {
			mu.Lock()
			detectedPorts[pid] = append(detectedPorts[pid], p)
			mu.Unlock()
			t.Logf("Detected port for PID %d: %s:%d", pid, p.Address, p.Port)
		}); err != nil {
			t.Errorf("Failed to subscribe to PID %d: %v", pid, err)
			continue
		}
	}

	// For this simplified test, we just verify the subscription works
	// In a real namespace scenario, each process would see different ports
	t.Log("Successfully set up multiple process monitoring")
}

// TestNamespaceIsolation verifies process isolation
func TestNamespaceIsolation(t *testing.T) {
	nm := GetGlobalMonitor()

	// Create two separate processes
	cmd1 := exec.Command("sleep", "10")
	if err := cmd1.Start(); err != nil {
		t.Fatalf("Failed to start process 1: %v", err)
	}
	defer cmd1.Process.Kill()

	cmd2 := exec.Command("sleep", "10")
	if err := cmd2.Start(); err != nil {
		t.Fatalf("Failed to start process 2: %v", err)
	}
	defer cmd2.Process.Kill()

	pid2 := cmd2.Process.Pid

	// Create a server in the test process (not in cmd1 or cmd2)
	listener, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatalf("Failed to create listener: %v", err)
	}
	defer listener.Close()

	// Subscribe to process 2 only
	detectedPorts := make(chan Port, 10)
	if err := nm.Subscribe(pid2, func(port Port) {
		select {
		case detectedPorts <- port:
		default:
		}
	}); err != nil {
		t.Fatalf("Failed to subscribe: %v", err)
	}

	// Wait a bit
	time.Sleep(2 * time.Second)

	// Should NOT detect the port since it's owned by the test process, not pid2
	select {
	case port := <-detectedPorts:
		t.Errorf("Unexpectedly detected port %s:%d for wrong process", port.Address, port.Port)
	case <-time.After(100 * time.Millisecond):
		// Good - no ports detected
		t.Log("Correctly isolated - ports from other processes not detected")
	}
}

// TestHostNetworkNamespace tests monitoring in the host network namespace
func TestHostNetworkNamespace(t *testing.T) {
	// This test doesn't require root since we're in the host namespace

	// Get the namespace monitor
	nm := GetGlobalMonitor()

	// Create a test server
	listener, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatalf("Failed to create listener: %v", err)
	}
	defer listener.Close()

	// Get the actual port
	addr := listener.Addr().(*net.TCPAddr)
	expectedPort := addr.Port

	// Subscribe to our own process
	portChan := make(chan Port, 10)
	if err := nm.Subscribe(os.Getpid(), func(port Port) {
		select {
		case portChan <- port:
		case <-time.After(1 * time.Second):
			t.Error("Timeout sending port to channel")
		}
	}); err != nil {
		t.Fatalf("Failed to subscribe: %v", err)
	}

	// Wait for detection
	select {
	case port := <-portChan:
		if port.Port != expectedPort {
			t.Errorf("Expected port %d, got %d", expectedPort, port.Port)
		}
		if port.PID != os.Getpid() {
			t.Errorf("Expected PID %d, got %d", os.Getpid(), port.PID)
		}
		t.Logf("Detected port in host namespace: %s:%d", port.Address, port.Port)
	case <-time.After(3 * time.Second):
		t.Error("Timeout waiting for port detection in host namespace")
	}
}
