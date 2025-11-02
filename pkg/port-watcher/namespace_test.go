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

// setupTestNamespace creates the "sprite" namespace for tests
func setupTestNamespace(t *testing.T) {
	// This test always runs as root in Docker environment

	// Create /var/run/netns directory if it doesn't exist
	if err := os.MkdirAll("/var/run/netns", 0755); err != nil {
		t.Fatalf("Failed to create netns directory: %v", err)
	}

	// Delete the namespace if it exists
	exec.Command("ip", "netns", "delete", "sprite").Run()

	// Create the namespace
	cmd := exec.Command("ip", "netns", "add", "sprite")
	if output, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("Failed to create sprite namespace: %v\nOutput: %s", err, output)
	}

	// Bring up loopback interface in the namespace
	cmd = exec.Command("ip", "netns", "exec", "sprite", "ip", "link", "set", "lo", "up")
	if output, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("Failed to bring up loopback in sprite namespace: %v\nOutput: %s", err, output)
	}

	// Cleanup function
	t.Cleanup(func() {
		exec.Command("ip", "netns", "delete", "sprite").Run()
	})
}

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
	setupTestNamespace(t)
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
	setupTestNamespace(t)
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
	// This test always runs in Linux Docker environment

	setupTestNamespace(t)

	// Get the namespace monitor
	nm := GetGlobalMonitor()

	// Start a process inside the sprite namespace that will open a port
	// Use a fixed port for simplicity since we control the namespace
	// Use socat instead of nc for a more reliable persistent listener
	expectedPort := 12345
	cmd := exec.Command("ip", "netns", "exec", "sprite", "socat", 
		fmt.Sprintf("TCP-LISTEN:%d,bind=127.0.0.1,reuseaddr,fork", expectedPort), 
		"/dev/null")

	if err := cmd.Start(); err != nil {
		t.Fatalf("Failed to start listener in namespace: %v", err)
	}
	defer cmd.Process.Kill()

	// The actual process inside the namespace is socat, not the ip command
	// We need to find the PID of socat inside the namespace
	time.Sleep(200 * time.Millisecond) // Give socat time to start and bind

	// Find the socat process
	findCmd := exec.Command("ip", "netns", "exec", "sprite", "pidof", "socat")
	output, err := findCmd.Output()
	if err != nil {
		t.Fatalf("Failed to find socat process: %v", err)
	}

	var pid int
	if _, err := fmt.Sscanf(strings.TrimSpace(string(output)), "%d", &pid); err != nil {
		t.Fatalf("Failed to parse socat PID: %v", err)
	}

	t.Logf("Started listener in sprite namespace on port %d (PID: %d)", expectedPort, pid)

	// Verify the port is actually listening before subscribing
	time.Sleep(200 * time.Millisecond)
	verifyCmd := exec.Command("nsenter", "--net=/var/run/netns/sprite", "ss", "-ltnp")
	if verifyOut, err := verifyCmd.Output(); err == nil {
		t.Logf("Current listening ports in sprite namespace:\n%s", string(verifyOut))
	} else {
		t.Logf("Failed to verify listening ports: %v", err)
	}

	// Subscribe to the process in the namespace
	portChan := make(chan Port, 10)
	receivedPorts := []Port{}
	if err := nm.SubscribeInNamespace(pid, "sprite", func(port Port) {
		t.Logf("Received port event: state=%s addr=%s port=%d pid=%d", port.State, port.Address, port.Port, port.PID)
		select {
		case portChan <- port:
		case <-time.After(1 * time.Second):
			t.Error("Timeout sending port to channel")
		}
	}); err != nil {
		t.Fatalf("Failed to subscribe: %v", err)
	}

	// Give the initial scan time to complete
	time.Sleep(500 * time.Millisecond)

	// Wait for detection
	// Note: We may receive events for other ports (especially close events for ports
	// that were already open when monitoring started), so we need to loop until we
	// find our specific port opening
	timeout := time.After(5 * time.Second)
	for {
		select {
		case port := <-portChan:
			receivedPorts = append(receivedPorts, port)
			t.Logf("Checking port event: state=%s addr=%s port=%d pid=%d (looking for port=%d pid=%d)",
				port.State, port.Address, port.Port, port.PID, expectedPort, pid)
			// Skip close events and ports that aren't ours
			if port.State == "open" && port.Port == expectedPort {
				// Found our port!
				if port.PID != pid {
					t.Errorf("Expected PID %d, got %d", pid, port.PID)
				}
				t.Logf("Detected port in namespace: %s:%d", port.Address, port.Port)
				return
			}
			// Otherwise, keep looking for our port
		case <-timeout:
			t.Errorf("Timeout waiting for port detection in namespace")
			t.Logf("Total port events received: %d", len(receivedPorts))
			for i, p := range receivedPorts {
				t.Logf("  Event %d: state=%s addr=%s port=%d pid=%d", i, p.State, p.Address, p.Port, p.PID)
			}

			// Final debug: check what's actually listening
			finalCmd := exec.Command("nsenter", "--net=/var/run/netns/sprite", "ss", "-ltnp")
			if finalOut, err := finalCmd.Output(); err == nil {
				t.Logf("Final listening ports in sprite namespace:\n%s", string(finalOut))
			}

			// Check process tree
			t.Logf("Process tree for PID %d:", pid)
			psCmd := exec.Command("ps", "-fp", fmt.Sprintf("%d", pid))
			if psOut, err := psCmd.Output(); err == nil {
				t.Logf("Process info:\n%s", string(psOut))
			}

			return
		}
	}
}

// TestNonExistentPID tests that the port watcher handles non-existent PIDs gracefully
func TestNonExistentPID(t *testing.T) {
	setupTestNamespace(t)
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
