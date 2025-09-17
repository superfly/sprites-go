package container

import (
	"os"
	"runtime"
	"testing"
)

func TestGetNamespacePID(t *testing.T) {
	if runtime.GOOS != "linux" {
		t.Skip("PID namespace tests only work on Linux")
	}

	// Test with current process (should return same PID if not in namespace)
	currentPID := os.Getpid()
	nsPID, err := getNamespacePID(currentPID)
	if err != nil {
		t.Errorf("Failed to get namespace PID for current process: %v", err)
	}

	// In a non-namespaced environment, namespace PID should equal host PID
	if nsPID != currentPID {
		t.Logf("Current process %d has namespace PID %d (might be in a container)", currentPID, nsPID)
	}
}

func TestResolvePID(t *testing.T) {
	if runtime.GOOS != "linux" {
		t.Skip("PID namespace tests only work on Linux")
	}

	// This test can only work meaningfully in a container environment
	// In a non-container environment, it should return an error for non-existent PIDs

	// Test with a PID that definitely doesn't exist in any namespace
	_, err := ResolvePID(999999)
	if err == nil {
		t.Error("Expected error for non-existent PID, got nil")
	}

	// Test with PID 1 (init) - should find something
	hostPID, err := ResolvePID(1)
	if err != nil {
		// This is OK - might not have any namespaced processes
		t.Logf("No process found with namespace PID 1: %v", err)
	} else {
		t.Logf("Found host PID %d for namespace PID 1", hostPID)
	}
}
