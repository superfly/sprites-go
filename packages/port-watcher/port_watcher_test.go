package portwatcher

import (
	"context"
	"fmt"
	"net"
	"os"
	"strconv"
	"strings"
	"testing"
	"time"
)

func TestParseTCPFile(t *testing.T) {
	// Mock /proc/net/tcp content
	mockTCP := `  sl  local_address rem_address   st tx_queue rx_queue tr tm->when retrnsmt   uid  timeout inode
   0: 0100007F:1F90 00000000:0000 0A 00000000:00000000 00:00000000 00000000  1000        0 12345 1 0000000000000000 100 0 0 10 0
   1: 00000000:0050 00000000:0000 0A 00000000:00000000 00:00000000 00000000     0        0 12346 1 0000000000000000 100 0 0 10 0
   2: 0100007F:22B8 00000000:0000 0A 00000000:00000000 00:00000000 00000000  1000        0 12347 1 0000000000000000 100 0 0 10 0`

	// Create a channel to collect detected ports
	detectedPorts := make(chan Port, 10)

	pw := &PortWatcher{
		pid:            os.Getpid(),
		portEventChan:  make(chan portEvent, 100),
		knownPortsChan: make(chan map[string]bool, 1),
	}

	// Initialize known ports
	pw.knownPortsChan <- make(map[string]bool)

	// Mock callback to collect ports
	pw.callback = func(port Port) {
		select {
		case detectedPorts <- port:
		case <-time.After(1 * time.Second):
			t.Error("Timeout sending port to channel")
		}
	}

	// Override findPIDForSocket to return our PID for testing
	pw.findPIDForSocket = func(inode string) int {
		if inode == "12345" || inode == "12347" {
			return os.Getpid()
		}
		return 0
	}

	// Start port event processor
	ctx, cancel := context.WithCancel(context.Background())
	pw.ctx = ctx
	pw.cancel = cancel
	defer cancel()

	// Start event processor without WaitGroup for testing
	go func() {
		for {
			select {
			case <-ctx.Done():
				return
			case event, ok := <-pw.portEventChan:
				if !ok {
					return
				}

				// Get current known ports
				knownPorts := <-pw.knownPortsChan

				// Check if this is a new port
				if !knownPorts[event.portKey] {
					knownPorts[event.portKey] = true
					// Trigger callback
					pw.callback(event.port)
				}

				// Put the map back
				select {
				case pw.knownPortsChan <- knownPorts:
				case <-ctx.Done():
					return
				}
			}
		}
	}()

	reader := strings.NewReader(mockTCP)
	err := pw.parseTCPFile(reader, false)
	if err != nil {
		t.Fatalf("Failed to parse TCP file: %v", err)
	}

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
	pw := &PortWatcher{}

	// Test with current process (should have a parent)
	ppid := pw.getParentPID(os.Getpid())
	if ppid == 0 {
		t.Error("Expected non-zero parent PID for current process")
	}

	// Test with PID 1 (init process, parent should be 0)
	ppid = pw.getParentPID(1)
	if ppid != 0 {
		t.Errorf("Expected parent PID 0 for init process, got %d", ppid)
	}
}

func TestIsPIDInTree(t *testing.T) {
	// Test with current PID
	pw := &PortWatcher{
		pid: os.Getpid(),
	}

	// Current PID should be in its own tree
	if !pw.isPIDInTree(os.Getpid()) {
		t.Error("Current PID should be in its own tree")
	}

	// PID 1 should not be in our tree (unless we're init, which is unlikely in tests)
	if os.Getpid() != 1 && pw.isPIDInTree(1) {
		t.Error("PID 1 should not be in our process tree")
	}
}

func TestPortWatcherIntegration(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
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

	// Create port watcher for current process
	pw, err := New(os.Getpid(), callback)
	if err != nil {
		t.Fatalf("Failed to create port watcher: %v", err)
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
	select {
	case port := <-portChan:
		if port.Port != expectedPort {
			t.Errorf("Expected port %d, got %d", expectedPort, port.Port)
		}
		if port.Address != "127.0.0.1" {
			t.Errorf("Expected address 127.0.0.1, got %s", port.Address)
		}
		if port.PID != os.Getpid() {
			t.Errorf("Expected PID %d, got %d", os.Getpid(), port.PID)
		}
	case <-time.After(5 * time.Second):
		t.Error("Timeout waiting for port detection")
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

func TestParseTCPFileExpandedAddresses(t *testing.T) {
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

	// Create a channel to collect detected ports
	detectedPorts := make(chan Port, 10)

	pw := &PortWatcher{
		pid:            os.Getpid(),
		portEventChan:  make(chan portEvent, 100),
		knownPortsChan: make(chan map[string]bool, 1),
	}

	// Initialize known ports
	pw.knownPortsChan <- make(map[string]bool)

	// Mock callback to collect ports
	pw.callback = func(port Port) {
		select {
		case detectedPorts <- port:
		case <-time.After(1 * time.Second):
			t.Error("Timeout sending port to channel")
		}
	}

	// Override findPIDForSocket to return our PID for testing
	pw.findPIDForSocket = func(inode string) int {
		// Return our PID for the addresses we want to monitor
		switch inode {
		case "12345", "12346", "12349", "12350": // localhost and all interfaces
			return os.Getpid()
		default:
			return 0 // Other addresses (like 10.0.0.1, 192.168.1.1) should be ignored
		}
	}

	// Start port event processor
	ctx, cancel := context.WithCancel(context.Background())
	pw.ctx = ctx
	pw.cancel = cancel
	defer cancel()

	// Start event processor
	go func() {
		for {
			select {
			case <-ctx.Done():
				return
			case event, ok := <-pw.portEventChan:
				if !ok {
					return
				}

				// Get current known ports
				knownPorts := <-pw.knownPortsChan

				// Check if this is a new port
				if !knownPorts[event.portKey] {
					knownPorts[event.portKey] = true
					// Trigger callback
					pw.callback(event.port)
				}

				// Put the map back
				select {
				case pw.knownPortsChan <- knownPorts:
				case <-ctx.Done():
					return
				}
			}
		}
	}()

	// Test IPv4 parsing
	reader := strings.NewReader(mockTCP)
	err := pw.parseTCPFile(reader, false)
	if err != nil {
		t.Fatalf("Failed to parse IPv4 TCP file: %v", err)
	}

	// Test IPv6 parsing
	reader6 := strings.NewReader(mockTCP6)
	err = pw.parseTCPFile(reader6, true)
	if err != nil {
		t.Fatalf("Failed to parse IPv6 TCP file: %v", err)
	}

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

	// Should detect 4 ports: 127.0.0.1:8080, 0.0.0.0:80, ::1:8080, :::80
	if len(ports) != 4 {
		t.Errorf("Expected 4 ports, got %d", len(ports))
		for _, port := range ports {
			t.Logf("Detected port: %s:%d", port.Address, port.Port)
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
