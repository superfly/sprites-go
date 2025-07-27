package portwatcher

import (
	"context"
	"fmt"
	"sync"
	"testing"
	"time"
)

// TestSSParsing verifies that ss output is parsed correctly
func TestSSParsing(t *testing.T) {
	nm := &NamespaceMonitor{
		subscribers: make(map[int][]*subscription),
		mu:          sync.RWMutex{},
	}

	watcher := &namespaceWatcher{
		namespaceID:  "test-namespace",
		namespacePID: 1,
		currentPorts: make(map[string]int),
		loggedAddrs:  make(map[string]bool),
		ctx:          context.Background(),
	}

	events := make(chan string, 10)

	// Subscribe to events
	nm.mu.Lock()
	nm.subscribers[9506] = []*subscription{
		{
			rootPID: 9506,
			callback: func(port Port) {
				events <- fmt.Sprintf("%s:%s:%d", port.State, port.Address, port.Port)
			},
		},
	}
	nm.mu.Unlock()

	// Test with the exact ss output from the user
	ssOutput := `State      Recv-Q     Send-Q         Local Address:Port          Peer Address:Port    Process
LISTEN     0          0                          *:54545                    *:*        users:(("claude",pid=9506,fd=29))`

	// Parse the output
	seenPorts := nm.parseSSOutput(ssOutput, watcher)

	// Should detect one port
	if len(seenPorts) != 1 {
		t.Errorf("Expected 1 port, got %d", len(seenPorts))
	}

	// Should be normalized to 0.0.0.0:54545
	if pid, exists := seenPorts["0.0.0.0:54545"]; !exists {
		t.Error("Port 0.0.0.0:54545 not found")
	} else if pid != 9506 {
		t.Errorf("Expected PID 9506, got %d", pid)
	}

	// Wait for event
	select {
	case event := <-events:
		if event != "open:0.0.0.0:54545" {
			t.Errorf("Expected open:0.0.0.0:54545, got %s", event)
		}
	case <-time.After(100 * time.Millisecond):
		t.Error("No event received")
	}
}

// TestSSParsingMultiplePorts tests parsing multiple ports
func TestSSParsingMultiplePorts(t *testing.T) {
	nm := &NamespaceMonitor{
		subscribers: make(map[int][]*subscription),
		mu:          sync.RWMutex{},
	}

	watcher := &namespaceWatcher{
		namespaceID:  "test-namespace",
		namespacePID: 1,
		currentPorts: make(map[string]int),
		loggedAddrs:  make(map[string]bool),
		ctx:          context.Background(),
	}

	// Subscribe to all events
	nm.mu.Lock()
	nm.subscribers[1000] = []*subscription{
		{
			rootPID: 1000,
			callback: func(port Port) {
				// Ignore events for this test
			},
		},
	}
	nm.mu.Unlock()

	// Test with multiple ports
	ssOutput := `State      Recv-Q     Send-Q         Local Address:Port          Peer Address:Port    Process
LISTEN     0          0                  127.0.0.1:8080                    *:*        users:(("app",pid=1000,fd=5))
LISTEN     0          0                          *:54545                    *:*        users:(("claude",pid=1000,fd=29))
LISTEN     0          0                         :::80                      :::*        users:(("nginx",pid=1000,fd=3))`

	seenPorts := nm.parseSSOutput(ssOutput, watcher)

	// Should detect 3 ports
	if len(seenPorts) != 3 {
		t.Errorf("Expected 3 ports, got %d", len(seenPorts))
	}

	expectedPorts := map[string]int{
		"127.0.0.1:8080": 1000,
		"0.0.0.0:54545":  1000,
		":::80":          1000,
	}

	for portKey, expectedPID := range expectedPorts {
		if pid, exists := seenPorts[portKey]; !exists {
			t.Errorf("Port %s not found", portKey)
		} else if pid != expectedPID {
			t.Errorf("Port %s: expected PID %d, got %d", portKey, expectedPID, pid)
		}
	}
}

// TestExtractPIDFromProcessInfo tests PID extraction from process info
func TestExtractPIDFromProcessInfo(t *testing.T) {
	nm := &NamespaceMonitor{}

	testCases := []struct {
		input    string
		expected int
	}{
		{`users:(("claude",pid=9506,fd=29))`, 9506},
		{`users:(("app",pid=1000,fd=5))`, 1000},
		{`users:(("nginx",pid=123,fd=3))`, 123},
		{`invalid`, 0},
		{`users:(("no-pid",fd=3))`, 0},
		{``, 0},
	}

	for _, tc := range testCases {
		result := nm.extractPIDFromProcessInfo(tc.input)
		if result != tc.expected {
			t.Errorf("Input %q: expected %d, got %d", tc.input, tc.expected, result)
		}
	}
}
