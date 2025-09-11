package portwatcher

import (
	"bytes"
	"context"
	"fmt"
	"log"
	"net"
	"os"
	"strconv"
	"strings"
	"sync" // Added for mutex initialization
	"testing"
	"time"
)

func TestNamespaceMonitorParsing(t *testing.T) {
	// Mock /proc/net/tcp content
	mockTCP := `  sl  local_address rem_address   st tx_queue rx_queue tr tm->when retrnsmt   uid  timeout inode
   0: 0100007F:1F90 00000000:0000 0A 00000000:00000000 00:00000000 00000000  1000        0 12345 1 0000000000000000 100 0 0 10 0
   1: 00000000:0050 00000000:0000 0A 00000000:00000000 00:00000000 00000000     0        0 12346 1 0000000000000000 100 0 0 10 0
   2: 0100007F:22B8 00000000:0000 0A 00000000:00000000 00:00000000 00000000  1000        0 12347 1 0000000000000000 100 0 0 10 0`

	// Create a namespace monitor for testing
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	nm := &NamespaceMonitor{
		monitors:     make(map[string]*namespaceWatcher),
		subscribers:  make(map[int][]*subscription),
		ctx:          ctx,
		cancel:       cancel,
		pollInterval: 1 * time.Second,
		mu:           sync.RWMutex{}, // Initialize the mutex
	}

	// Create a mock namespace watcher
	watcher := &namespaceWatcher{
		namespaceID:  "test-namespace",
		currentPorts: make(map[string]int),
		loggedAddrs:  make(map[string]bool),
	}

	// Collect detected ports
	detectedPorts := make(chan Port, 10)

	// Add a subscription
	nm.mu.Lock()
	nm.subscribers[os.Getpid()] = []*subscription{
		{
			rootPID: os.Getpid(),
			callback: func(port Port) {
				select {
				case detectedPorts <- port:
				case <-time.After(1 * time.Second):
					t.Error("Timeout sending port to channel")
				}
			},
		},
	}
	nm.mu.Unlock()

	// Override the global findPIDForSocket for testing
	oldFindPIDForSocket := findPIDForSocketFunc
	findPIDForSocketFunc = func(inode string) int {
		if inode == "12345" || inode == "12347" {
			return os.Getpid()
		}
		return 0
	}
	defer func() { findPIDForSocketFunc = oldFindPIDForSocket }()

	// Parse the mock data
	reader := strings.NewReader(mockTCP)
	nm.parseAndNotify(reader, watcher, false)

	// Wait a bit for processing
	time.Sleep(100 * time.Millisecond)

	// Collect results
	var ports []Port
	done := false
	for !done {
		select {
		case port := <-detectedPorts:
			ports = append(ports, port)
		case <-time.After(100 * time.Millisecond):
			done = true
		}
	}

	// Should detect ports 8080 (0x1F90) and 8888 (0x22B8) on 127.0.0.1
	if len(ports) != 2 {
		t.Errorf("Expected 2 ports, got %d", len(ports))
	}

	// Check ports
	foundPort8080 := false
	foundPort8888 := false
	for _, port := range ports {
		if port.Port == 8080 && port.Address == "127.0.0.1" {
			foundPort8080 = true
		}
		if port.Port == 8888 && port.Address == "127.0.0.1" {
			foundPort8888 = true
		}
	}

	if !foundPort8080 {
		t.Error("Port 8080 not detected")
	}
	if !foundPort8888 {
		t.Error("Port 8888 not detected")
	}
}

func TestGetParentPID(t *testing.T) {
	// Skip on non-Linux systems
	if _, err := os.Stat("/proc/self/stat"); err != nil {
		t.Skip("Skipping test on non-Linux system")
	}

	// Test with current process (should have a parent)
	ppid := getParentPID(os.Getpid())
	// In containers or certain environments, ppid might be 0
	if ppid < 0 {
		t.Error("Expected non-negative parent PID for current process")
	}

	// Test with PID 1 (init process, parent should be 0)
	ppid = getParentPID(1)
	if ppid != 0 {
		t.Errorf("Expected parent PID 0 for init process, got %d", ppid)
	}
}

func TestIsPIDInTree(t *testing.T) {
	// Current PID should be in its own tree
	if !isPIDInTree(os.Getpid(), os.Getpid()) {
		t.Error("Current PID should be in its own tree")
	}

	// PID 1 should not be in our tree (unless we're init, which is unlikely in tests)
	if os.Getpid() != 1 && isPIDInTree(1, os.Getpid()) {
		t.Error("PID 1 should not be in our process tree")
	}
}

func TestPortWatcherIntegration(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	// Skip on non-Linux systems
	if _, err := os.Stat("/proc/self/ns/net"); err != nil {
		t.Skip("Skipping test on non-Linux system")
	}

	// Create a channel to receive port notifications
	portChan := make(chan Port, 10)
	callback := func(port Port) {
		select {
		case portChan <- port:
		case <-time.After(1 * time.Second):
			t.Error("Timeout sending port to channel")
		}
	}

	// Create port watcher directly without container PID resolution
	// since this is a test process, not a container
	pw := &PortWatcher{
		pids:     []int{os.Getpid()},
		callback: callback,
		monitor:  GetGlobalMonitor(),
	}
	defer pw.Stop()

	// Start watching
	if err := pw.Start(); err != nil {
		t.Fatalf("Failed to start port watcher: %v", err)
	}

	// Give it a moment to do initial scan
	time.Sleep(100 * time.Millisecond)

	// Start a listener on localhost
	listener, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatalf("Failed to create listener: %v", err)
	}
	defer listener.Close()

	// Get the port
	addr := listener.Addr().(*net.TCPAddr)
	expectedPort := addr.Port

	// Wait for the port to be detected
	// Note: We may receive events for other ports (especially close events for ports
	// that were already open when monitoring started), so we need to loop until we
	// find our specific port opening
	timeout := time.After(5 * time.Second)
	for {
		select {
		case port := <-portChan:
			// Skip close events and ports that aren't ours
			if port.State == "open" && port.Port == expectedPort {
				// Found our port!
				if port.Address != "127.0.0.1" {
					t.Errorf("Expected address 127.0.0.1, got %s", port.Address)
				}
				if port.PID != os.Getpid() {
					t.Errorf("Expected PID %d, got %d", os.Getpid(), port.PID)
				}
				// Success - we found our port
				return
			}
			// Otherwise, keep looking for our port
		case <-timeout:
			t.Error("Timeout waiting for port detection")
			return
		}
	}
}

func TestPortHexConversion(t *testing.T) {
	tests := []struct {
		hex      string
		expected int
	}{
		{"1F90", 8080},
		{"0050", 80},
		{"22B8", 8888},
		{"01BB", 443},
	}

	for _, test := range tests {
		port64, err := strconv.ParseInt(test.hex, 16, 32)
		if err != nil {
			t.Errorf("Failed to parse hex %s: %v", test.hex, err)
			continue
		}
		port := int(port64)
		if port != test.expected {
			t.Errorf("Hex %s: expected port %d, got %d", test.hex, test.expected, port)
		}
	}
}

func TestIPv4AddressConversion(t *testing.T) {
	tests := []struct {
		hex      string
		expected string
	}{
		{"0100007F", "127.0.0.1"},
		{"00000000", "0.0.0.0"},
		{"0200007F", "127.0.0.2"},
		{"FFFFFFFF", "255.255.255.255"},
	}

	for _, test := range tests {
		addrInt, err := strconv.ParseUint(test.hex, 16, 32)
		if err != nil {
			t.Errorf("Failed to parse hex %s: %v", test.hex, err)
			continue
		}

		b1 := byte(addrInt & 0xFF)
		b2 := byte((addrInt >> 8) & 0xFF)
		b3 := byte((addrInt >> 16) & 0xFF)
		b4 := byte((addrInt >> 24) & 0xFF)

		addr := fmt.Sprintf("%d.%d.%d.%d", b1, b2, b3, b4)
		if addr != test.expected {
			t.Errorf("Hex %s: expected IP %s, got %s", test.hex, test.expected, addr)
		}
	}
}

func TestParseTCPDataExpandedAddresses(t *testing.T) {
	// Mock /proc/net/tcp content with various addresses
	mockTCP := `  sl  local_address rem_address   st tx_queue rx_queue tr tm->when retrnsmt   uid  timeout inode
   0: 0100007F:1F90 00000000:0000 0A 00000000:00000000 00:00000000 00000000  1000        0 12345 1 0000000000000000 100 0 0 10 0
   1: 00000000:0050 00000000:0000 0A 00000000:00000000 00:00000000 00000000  1000        0 12346 1 0000000000000000 100 0 0 10 0
   2: 0A000001:8080 00000000:0000 0A 00000000:00000000 00:00000000 00000000  1000        0 12347 1 0000000000000000 100 0 0 10 0
   3: C0A80101:3000 00000000:0000 0A 00000000:00000000 00:00000000 00000000  1000        0 12348 1 0000000000000000 100 0 0 10 0`

	// Mock /proc/net/tcp6 content
	mockTCP6 := `  sl  local_address                         remote_address                        st tx_queue rx_queue tr tm->when retrnsmt   uid  timeout inode
   0: 00000000000000000000000001000000:1F90 00000000000000000000000000000000:0000 0A 00000000:00000000 00:00000000 00000000  1000        0 12349 1 0000000000000000 100 0 0 10 0
   1: 00000000000000000000000000000000:0050 00000000000000000000000000000000:0000 0A 00000000:00000000 00:00000000 00000000  1000        0 12350 1 0000000000000000 100 0 0 10 0
   2: 20010DB80000000000000000000000001:8080 00000000000000000000000000000000:0000 0A 00000000:00000000 00:00000000 00000000  1000        0 12351 1 0000000000000000 100 0 0 10 0`

	// Create a namespace monitor for testing
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	nm := &NamespaceMonitor{
		monitors:     make(map[string]*namespaceWatcher),
		subscribers:  make(map[int][]*subscription),
		ctx:          ctx,
		cancel:       cancel,
		pollInterval: 1 * time.Second,
		mu:           sync.RWMutex{}, // Initialize the mutex
	}

	// Create a mock namespace watcher
	watcher := &namespaceWatcher{
		namespaceID:  "test-namespace",
		currentPorts: make(map[string]int),
		loggedAddrs:  make(map[string]bool),
	}

	// Collect detected ports
	detectedPorts := make(chan Port, 10)

	// Add a subscription
	nm.mu.Lock()
	nm.subscribers[os.Getpid()] = []*subscription{
		{
			rootPID: os.Getpid(),
			callback: func(port Port) {
				select {
				case detectedPorts <- port:
				case <-time.After(1 * time.Second):
					t.Error("Timeout sending port to channel")
				}
			},
		},
	}
	nm.mu.Unlock()

	// Override the global findPIDForSocket for testing
	oldFindPIDForSocket := findPIDForSocketFunc
	findPIDForSocketFunc = func(inode string) int {
		// Return our PID for the addresses we want to monitor
		switch inode {
		case "12345", "12346", "12349", "12350": // localhost and all interfaces
			return os.Getpid()
		default:
			return 0 // Other addresses (like 10.0.0.1, 192.168.1.1) should be ignored
		}
	}
	defer func() { findPIDForSocketFunc = oldFindPIDForSocket }()

	// Test IPv4 parsing
	reader := strings.NewReader(mockTCP)
	nm.parseAndNotify(reader, watcher, false)

	// Test IPv6 parsing
	reader6 := strings.NewReader(mockTCP6)
	nm.parseAndNotify(reader6, watcher, true)

	// Wait a bit for processing
	time.Sleep(100 * time.Millisecond)

	// Collect results
	var ports []Port
	done := false
	for !done {
		select {
		case port := <-detectedPorts:
			ports = append(ports, port)
		case <-time.After(100 * time.Millisecond):
			done = true
		}
	}

	// We should have detected exactly 4 open ports
	openPorts := 0
	for _, port := range ports {
		if port.State == "open" {
			openPorts++
		}
	}
	if openPorts != 4 {
		t.Errorf("Expected 4 open ports, got %d", openPorts)
		for i, port := range ports {
			t.Logf("Port %d: %s:%d state=%s", i, port.Address, port.Port, port.State)
		}
	}

	// Check specific ports
	expectedPorts := map[string]int{
		"127.0.0.1": 8080,
		"0.0.0.0":   80,
		"::1":       8080,
		"::":        80,
	}

	foundPorts := make(map[string]int)
	for _, port := range ports {
		foundPorts[port.Address] = port.Port
	}

	for expectedAddr, expectedPort := range expectedPorts {
		if foundPort, found := foundPorts[expectedAddr]; !found {
			t.Errorf("Expected port on %s not found", expectedAddr)
		} else if foundPort != expectedPort {
			t.Errorf("Expected port %d on %s, got %d", expectedPort, expectedAddr, foundPort)
		}
	}
}

// TestPortDeduplication verifies that the same address:port is only reported once
func TestPortDeduplication(t *testing.T) {
	nm := &NamespaceMonitor{
		subscribers: make(map[int][]*subscription),
		mu:          sync.RWMutex{},
	}

	watcher := &namespaceWatcher{
		namespaceID:  "test-namespace",
		currentPorts: make(map[string]int),
		loggedAddrs:  make(map[string]bool),
	}

	notificationsChan := make(chan int, 10)
	nm.mu.Lock()
	nm.subscribers[2220] = []*subscription{
		{
			rootPID: 2220,
			callback: func(port Port) {
				if port.Port == 8080 && port.Address == "127.0.0.1" {
					notificationsChan <- 1
				}
			},
		},
	}
	nm.mu.Unlock()

	// Mock findPIDForSocket to return the same PID
	oldFindPIDForSocket := findPIDForSocketFunc
	findPIDForSocketFunc = func(inode string) int {
		return 2220
	}
	defer func() { findPIDForSocketFunc = oldFindPIDForSocket }()

	// First scan with port 8080 appearing once
	mockTCP := `  sl  local_address rem_address   st tx_queue rx_queue tr tm->when retrnsmt   uid  timeout inode
   0: 0100007F:1F90 00000000:0000 0A 00000000:00000000 00:00000000 00000000  1000        0 12345 1 0000000000000000 100 0 0 10 0`

	seenPorts := nm.parseAndNotify(strings.NewReader(mockTCP), watcher, false)

	// Update currentPorts
	for k, v := range seenPorts {
		watcher.currentPorts[k] = v
	}

	// Wait for notification
	select {
	case <-notificationsChan:
		// Good - got notification
	case <-time.After(100 * time.Millisecond):
		t.Error("Did not receive expected notification")
		return
	}

	// Second scan with the same port
	nm.parseAndNotify(strings.NewReader(mockTCP), watcher, false)

	// Should NOT receive another notification
	select {
	case <-notificationsChan:
		t.Error("Received unexpected duplicate notification for port 8080")
	case <-time.After(100 * time.Millisecond):
		// Good - no duplicate
	}
}

func TestPortOpenClose(t *testing.T) {
	nm := &NamespaceMonitor{
		subscribers: make(map[int][]*subscription),
		monitors:    make(map[string]*namespaceWatcher),
		mu:          sync.RWMutex{},
	}

	portEvents := make(chan Port, 10)

	// Subscribe to a PID
	nm.mu.Lock()
	nm.subscribers[44789] = []*subscription{
		{
			rootPID: 44789,
			callback: func(port Port) {
				portEvents <- port
			},
		},
	}
	nm.mu.Unlock()

	watcher := &namespaceWatcher{
		namespaceID: "test-namespace",

		currentPorts: make(map[string]int),
		loggedAddrs:  make(map[string]bool),
	}

	// Mock findPIDForSocket
	oldFindPIDForSocket := findPIDForSocketFunc
	findPIDForSocketFunc = func(inode string) int {
		if inode == "12345" {
			return 44789
		}
		return 0
	}
	defer func() { findPIDForSocketFunc = oldFindPIDForSocket }()

	// First scan - port 8080 is open
	mockTCP1 := `  sl  local_address rem_address   st tx_queue rx_queue tr tm->when retrnsmt   uid  timeout inode
   0: 0100007F:1F90 00000000:0000 0A 00000000:00000000 00:00000000 00000000  1000        0 12345 1 0000000000000000 100 0 0 10 0`

	// parseAndNotify returns seen ports
	seenPorts1 := nm.parseAndNotify(strings.NewReader(mockTCP1), watcher, false)

	// Update currentPorts manually (as scanNamespace would do)
	for k, v := range seenPorts1 {
		watcher.currentPorts[k] = v
	}

	// Should receive open notification
	select {
	case port := <-portEvents:
		if port.Port != 8080 || port.Address != "127.0.0.1" || port.State != "open" {
			t.Errorf("Expected open event for 127.0.0.1:8080, got %s:%d state=%s",
				port.Address, port.Port, port.State)
		}
	case <-time.After(100 * time.Millisecond):
		t.Error("Did not receive expected open notification")
	}

	// Second scan - port 8080 is gone
	mockTCP2 := `  sl  local_address rem_address   st tx_queue rx_queue tr tm->when retrnsmt   uid  timeout inode`

	seenPorts2 := nm.parseAndNotify(strings.NewReader(mockTCP2), watcher, false)

	// Simulate scanNamespace behavior - detect closed ports
	for portKey, pid := range watcher.currentPorts {
		if _, stillExists := seenPorts2[portKey]; !stillExists {
			// Port was closed
			parts := strings.Split(portKey, ":")
			if len(parts) >= 2 {
				portStr := parts[len(parts)-1]
				port, _ := strconv.Atoi(portStr)
				addr := strings.Join(parts[:len(parts)-1], ":")

				log.Printf("Port watcher: port closed in namespace %s - %s (PID: %d)",
					watcher.namespaceID, portKey, pid)

				nm.notifySubscribers(Port{
					Port:    port,
					PID:     pid,
					Address: addr,
					State:   "closed",
				})
			}
		}
	}

	// Update currentPorts
	watcher.currentPorts = seenPorts2

	// Should receive close notification
	select {
	case port := <-portEvents:
		if port.Port != 8080 || port.Address != "127.0.0.1" || port.State != "closed" {
			t.Errorf("Expected close event for 127.0.0.1:8080, got %s:%d state=%s",
				port.Address, port.Port, port.State)
		}
	case <-time.After(100 * time.Millisecond):
		t.Error("Did not receive expected close notification")
	}

	// Third scan - port 8080 is back
	seenPorts3 := nm.parseAndNotify(strings.NewReader(mockTCP1), watcher, false)

	// Update currentPorts
	for k, v := range seenPorts3 {
		watcher.currentPorts[k] = v
	}

	// Should receive open notification again
	select {
	case port := <-portEvents:
		if port.Port != 8080 || port.Address != "127.0.0.1" || port.State != "open" {
			t.Errorf("Expected second open event for 127.0.0.1:8080, got %s:%d state=%s",
				port.Address, port.Port, port.State)
		}
	case <-time.After(100 * time.Millisecond):
		t.Error("Did not receive expected second open notification")
	}
}

// TestHexToIPv6 verifies IPv6 hex to readable format conversion
func TestHexToIPv6(t *testing.T) {
	tests := []struct {
		hex      string
		expected string
	}{
		{
			hex:      "00000000000000000000000000000001",
			expected: "0000:0000:0000:0000:0000:0000:0000:0001",
		},
		{
			hex:      "20010DB8000000000000000000000001",
			expected: "2001:0db8:0000:0000:0000:0000:0000:0001",
		},
		{
			hex:      "404C052601C418012A9C00000100DE2A",
			expected: "404c:0526:01c4:1801:2a9c:0000:0100:de2a",
		},
		{
			hex:      "00000000000000000000000000000000",
			expected: "0000:0000:0000:0000:0000:0000:0000:0000",
		},
		{
			hex:      "invalid", // Too short
			expected: "invalid",
		},
	}

	for _, tt := range tests {
		t.Run(tt.hex, func(t *testing.T) {
			result := hexToIPv6(tt.hex)
			if result != tt.expected {
				t.Errorf("hexToIPv6(%s) = %s, want %s", tt.hex, result, tt.expected)
			}
		})
	}
}

// TestPortPersistenceAcrossScans verifies that ports don't repeatedly show as "new" across scans
func TestPortPersistenceAcrossScans(t *testing.T) {
	nm := &NamespaceMonitor{
		subscribers: make(map[int][]*subscription),
		mu:          sync.RWMutex{},
	}

	watcher := &namespaceWatcher{
		namespaceID: "test-namespace",

		currentPorts: make(map[string]int),
		loggedAddrs:  make(map[string]bool),
	}

	portEventsChan := make(chan string, 10)

	// Subscribe to a PID
	nm.mu.Lock()
	nm.subscribers[2220] = []*subscription{
		{
			rootPID: 2220,
			callback: func(port Port) {
				event := fmt.Sprintf("%s port %s:%d (PID: %d)",
					port.State, port.Address, port.Port, port.PID)
				portEventsChan <- event
				t.Logf("Event: %s", event)
			},
		},
	}
	nm.mu.Unlock()

	// Mock findPIDForSocket
	oldFindPIDForSocket := findPIDForSocketFunc
	findPIDForSocketFunc = func(inode string) int {
		return 2220
	}
	defer func() { findPIDForSocketFunc = oldFindPIDForSocket }()

	// Mock TCP data with a port
	mockTCP := `  sl  local_address rem_address   st tx_queue rx_queue tr tm->when retrnsmt   uid  timeout inode
   0: 0100007F:1F90 00000000:0000 0A 00000000:00000000 00:00000000 00000000  1000        0 12345 1 0000000000000000 100 0 0 10 0`

	// First scan
	seenPorts1 := nm.parseAndNotify(strings.NewReader(mockTCP), watcher, false)
	for k, v := range seenPorts1 {
		watcher.currentPorts[k] = v
	}

	// Wait for first event
	select {
	case event := <-portEventsChan:
		if !strings.Contains(event, "open") || !strings.Contains(event, "8080") {
			t.Errorf("Expected open event for port 8080, got: %s", event)
		}
	case <-time.After(100 * time.Millisecond):
		t.Error("Did not receive expected first event")
		return
	}

	// Second scan - same data
	seenPorts2 := nm.parseAndNotify(strings.NewReader(mockTCP), watcher, false)
	for k, v := range seenPorts2 {
		watcher.currentPorts[k] = v
	}

	// Third scan - same data
	seenPorts3 := nm.parseAndNotify(strings.NewReader(mockTCP), watcher, false)
	for k, v := range seenPorts3 {
		watcher.currentPorts[k] = v
	}

	// Should NOT receive any more events
	select {
	case event := <-portEventsChan:
		t.Errorf("Received unexpected duplicate event: %s", event)
	case <-time.After(100 * time.Millisecond):
		// Good - no more events
	}
}

// TestUnmonitoredPortsNoRepeatLogs verifies that ports from unmonitored processes don't generate repeated log messages
func TestUnmonitoredPortsNoRepeatLogs(t *testing.T) {
	// Create a custom NamespaceMonitor so we can control logging
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	nm := &NamespaceMonitor{
		monitors:     make(map[string]*namespaceWatcher),
		subscribers:  make(map[int][]*subscription),
		ctx:          ctx,
		cancel:       cancel,
		pollInterval: 1 * time.Second,
		mu:           sync.RWMutex{},
	}

	watcher := &namespaceWatcher{

		namespaceID:  "test-namespace",
		currentPorts: make(map[string]int),
		loggedAddrs:  make(map[string]bool),
	}

	// Capture log output
	var logBuffer bytes.Buffer
	oldLogOutput := log.Writer()
	log.SetOutput(&logBuffer)
	defer log.SetOutput(oldLogOutput)

	// Override findPIDForSocket to return a PID not in any tree
	oldFindPIDForSocket := findPIDForSocketFunc
	findPIDForSocketFunc = func(inode string) int {
		return 9999 // Not in any monitored tree
	}
	defer func() { findPIDForSocketFunc = oldFindPIDForSocket }()

	// Add a subscription for a different PID
	nm.mu.Lock()
	nm.subscribers[1234] = []*subscription{
		{
			rootPID: 1234,
			callback: func(port Port) {
				// Should never be called for PID 9999
			},
		},
	}
	nm.mu.Unlock()

	// Mock TCP data with a port from unmonitored process
	mockTCP := `  sl  local_address rem_address   st tx_queue rx_queue tr tm->when retrnsmt   uid  timeout inode
   0: 0100007F:1F90 00000000:0000 0A 00000000:00000000 00:00000000 00000000  1000        0 12345 1 0000000000000000 100 0 0 10 0`

	// First scan
	logBuffer.Reset()
	seenPorts1 := nm.parseAndNotify(strings.NewReader(mockTCP), watcher, false)
	// Update currentPorts as scanNamespace would do
	for k, v := range seenPorts1 {
		watcher.currentPorts[k] = v
	}
	firstScanLogs := logBuffer.String()

	// Second scan with same data
	logBuffer.Reset()
	seenPorts2 := nm.parseAndNotify(strings.NewReader(mockTCP), watcher, false)
	// Update currentPorts again
	for k, v := range seenPorts2 {
		watcher.currentPorts[k] = v
	}
	secondScanLogs := logBuffer.String()

	// Third scan
	logBuffer.Reset()
	seenPorts3 := nm.parseAndNotify(strings.NewReader(mockTCP), watcher, false)
	// Update currentPorts again
	for k, v := range seenPorts3 {
		watcher.currentPorts[k] = v
	}
	thirdScanLogs := logBuffer.String()

	// Log the results for debugging
	t.Logf("First scan logs:\n%s", firstScanLogs)
	t.Logf("Second scan logs:\n%s", secondScanLogs)
	t.Logf("Third scan logs:\n%s", thirdScanLogs)

	// With the new implementation, unmonitored ports should NOT generate any logs at all
	if len(strings.TrimSpace(firstScanLogs)) > 0 {
		t.Errorf("First scan should not log anything for unmonitored port, but got: %s", firstScanLogs)
	}

	// Second and third scans should also have NO log messages
	if len(strings.TrimSpace(secondScanLogs)) > 0 {
		t.Errorf("Second scan should not log anything for unmonitored port, but got: %s", secondScanLogs)
	}

	if len(strings.TrimSpace(thirdScanLogs)) > 0 {
		t.Errorf("Third scan should not log anything for unmonitored port, but got: %s", thirdScanLogs)
	}

	// Verify the port is being tracked internally by checking it doesn't generate new notifications
	var notificationCount int
	nm.mu.Lock()
	nm.subscribers[1234] = []*subscription{
		{
			rootPID: 1234,
			callback: func(port Port) {
				notificationCount++
			},
		},
	}
	nm.mu.Unlock()

	// Even though we're not monitoring this port, it should be tracked in currentPorts
	if len(watcher.currentPorts) != 1 {
		t.Errorf("Expected 1 port in currentPorts, got %d", len(watcher.currentPorts))
	}

	// Verify the port is tracked with correct PID
	if pid, exists := watcher.currentPorts["127.0.0.1:8080"]; !exists || pid != 9999 {
		t.Errorf("Port 127.0.0.1:8080 should be tracked with PID 9999, got exists=%v pid=%d", exists, pid)
	}
}
