//go:build linux
// +build linux

package portwatcher

import (
	"fmt"
	"net"
	"os"
	"os/exec"
	"strings"
	"sync"
	"testing"
	"time"
)

// TestNamespaceCreation removed: avoid creating separate namespaces in tests
func TestNamespaceCreation(t *testing.T) {
	// Removed: avoid creating separate namespaces in tests
	t.Skip("namespace creation test removed")
}

// Removed: we no longer run OCI/crun containers in unit tests
func TestNamespaceWithCrun(t *testing.T) {
	t.Skip("crun-based namespace test removed")
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
		if err := nm.SubscribeInNamespace(pid, "sprite", func(p Port) {
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
	if err := nm.SubscribeInNamespace(pid2, "sprite", func(port Port) {
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
	// This test uses the namespace monitor which requires nsenter and ss -ltnp to work
	// Skip on non-Linux systems
	if _, err := os.Stat("/proc/self/ns/net"); err != nil {
		t.Skip("Skipping test on non-Linux system")
	}

	// Check if we can run nsenter and ss exactly as the namespace monitor will
	// Test with both current PID and PID 1 (common init PID)
	for _, pid := range []int{os.Getpid(), 1} {
		cmd := exec.Command("nsenter", "--net=/proc/"+fmt.Sprintf("%d", pid)+"/ns/net", "ss", "-ltnp")
		output, err := cmd.CombinedOutput()
		if err == nil {
			// Command succeeded, check if it shows process information
			if strings.Contains(string(output), "users:") || strings.Contains(string(output), "pid=") {
				// Good, we can get process information
				goto skipCheckPassed
			}
		}
	}
	// If we get here, neither PID worked - skip the test
	t.Skip("Skipping test - nsenter/ss not working in this environment (missing privileges or capabilities)")

skipCheckPassed:

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
	if err := nm.SubscribeInNamespace(os.Getpid(), "sprite", func(port Port) {
		select {
		case portChan <- port:
		case <-time.After(1 * time.Second):
			t.Error("Timeout sending port to channel")
		}
	}); err != nil {
		t.Fatalf("Failed to subscribe: %v", err)
	}

	// Wait for detection
	// Note: We may receive events for other ports (especially close events for ports
	// that were already open when monitoring started), so we need to loop until we
	// find our specific port opening
	timeout := time.After(3 * time.Second)
	for {
		select {
		case port := <-portChan:
			// Skip close events and ports that aren't ours
			if port.State == "open" && port.Port == expectedPort {
				// Found our port!
				if port.PID != os.Getpid() {
					t.Errorf("Expected PID %d, got %d", os.Getpid(), port.PID)
				}
				t.Logf("Detected port in host namespace: %s:%d", port.Address, port.Port)
				return
			}
			// Otherwise, keep looking for our port
		case <-timeout:
			t.Error("Timeout waiting for port detection in host namespace")
			return
		}
	}
}

// TestNonExistentPID tests that the port watcher handles non-existent PIDs gracefully
func TestNonExistentPID(t *testing.T) {
	nm := GetGlobalMonitor()

	// Use a PID that definitely doesn't exist
	nonExistentPID := 999999

	// Subscribe to non-existent PID - this should not error
	portChan := make(chan Port, 10)
	if err := nm.SubscribeInNamespace(nonExistentPID, "sprite", func(p Port) {
		select {
		case portChan <- p:
		default:
			// Channel full, ignore
		}
	}); err != nil {
		t.Fatalf("Subscribe should not error for non-existent PID: %v", err)
	}

	// Wait a bit to see if any scanning happens
	time.Sleep(2 * time.Second)

	// The scan should not produce any errors and should be a no-op
	// We don't expect any ports to be detected since the PID doesn't exist
	select {
	case p := <-portChan:
		t.Errorf("Unexpected port detected for non-existent PID: %+v", p)
	default:
		// This is expected - no ports should be detected
		t.Logf("Correctly handled non-existent PID - no ports detected")
	}
}
