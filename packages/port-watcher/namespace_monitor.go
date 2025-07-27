package portwatcher

import (
	"bufio"
	"context"
	"fmt"
	"io"
	"log"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"
)

// NamespaceMonitor manages port monitoring for all network namespaces
type NamespaceMonitor struct {
	mu           sync.RWMutex
	monitors     map[string]*namespaceWatcher // key is namespace inode
	subscribers  map[int][]*subscription      // key is PID
	ctx          context.Context
	cancel       context.CancelFunc
	pollInterval time.Duration
}

// namespaceWatcher monitors a specific network namespace
type namespaceWatcher struct {
	namespaceID  string
	namespacePID int
	knownPorts   map[string]bool // key: "addr:port"
	loggedAddrs  map[string]bool // key: "addr:port" for unrecognized addresses
	ctx          context.Context
	cancel       context.CancelFunc
}

// subscription represents a subscription to port events for a PID tree
type subscription struct {
	rootPID  int
	callback PortCallback
}

// portDetection represents a detected port in a namespace
type portDetection struct {
	port        Port
	namespaceID string
}

var (
	globalMonitor     *NamespaceMonitor
	globalMonitorOnce sync.Once
)

// GetGlobalMonitor returns the singleton namespace monitor
func GetGlobalMonitor() *NamespaceMonitor {
	globalMonitorOnce.Do(func() {
		ctx, cancel := context.WithCancel(context.Background())
		globalMonitor = &NamespaceMonitor{
			monitors:     make(map[string]*namespaceWatcher),
			subscribers:  make(map[int][]*subscription),
			ctx:          ctx,
			cancel:       cancel,
			pollInterval: 1 * time.Second,
		}
		go globalMonitor.run()
	})
	return globalMonitor
}

// Subscribe subscribes to port events for a PID and its children
func (nm *NamespaceMonitor) Subscribe(pid int, callback PortCallback) error {
	nm.mu.Lock()
	defer nm.mu.Unlock()

	// Find the namespace for this PID
	namespaceID, err := getNetworkNamespace(pid)
	if err != nil {
		return fmt.Errorf("failed to get namespace for PID %d: %w", pid, err)
	}

	log.Printf("Port watcher: PID %d is in namespace %s", pid, namespaceID)

	// Find or create the namespace watcher
	if _, exists := nm.monitors[namespaceID]; !exists {
		// Find PID 1 in this namespace
		namespacePID, err := findNamespacePID1(namespaceID)
		if err != nil {
			return fmt.Errorf("failed to find namespace PID 1: %w", err)
		}

		// Create a new namespace watcher
		ctx, cancel := context.WithCancel(nm.ctx)
		watcher := &namespaceWatcher{
			namespacePID: namespacePID,
			namespaceID:  namespaceID,
			knownPorts:   make(map[string]bool),
			loggedAddrs:  make(map[string]bool),
			ctx:          ctx,
			cancel:       cancel,
		}
		nm.monitors[namespaceID] = watcher

		// Start monitoring this namespace
		go nm.monitorNamespace(watcher)

		log.Printf("Port watcher: started monitoring namespace %s via PID %d", namespaceID, namespacePID)
	}

	// Add the subscription
	sub := &subscription{
		rootPID:  pid,
		callback: callback,
	}
	nm.subscribers[pid] = append(nm.subscribers[pid], sub)

	log.Printf("Port watcher: subscribed to PID %d in namespace %s", pid, namespaceID)
	return nil
}

// Unsubscribe removes a subscription for a PID
func (nm *NamespaceMonitor) Unsubscribe(pid int) {
	nm.mu.Lock()
	defer nm.mu.Unlock()

	delete(nm.subscribers, pid)

	// TODO: Clean up namespace watchers with no subscribers
}

// Stop stops the global monitor
func (nm *NamespaceMonitor) Stop() {
	nm.cancel()
}

// run is the main loop for the namespace monitor
func (nm *NamespaceMonitor) run() {
	<-nm.ctx.Done()

	// Stop all namespace watchers
	nm.mu.Lock()
	for _, watcher := range nm.monitors {
		watcher.cancel()
	}
	nm.mu.Unlock()
}

// monitorNamespace monitors a single network namespace
func (nm *NamespaceMonitor) monitorNamespace(watcher *namespaceWatcher) {
	ticker := time.NewTicker(nm.pollInterval)
	defer ticker.Stop()

	for {
		select {
		case <-watcher.ctx.Done():
			return
		case <-ticker.C:
			nm.scanNamespace(watcher)
		}
	}
}

// scanNamespace scans for new ports in a namespace
func (nm *NamespaceMonitor) scanNamespace(watcher *namespaceWatcher) {
	// Use nsenter to read TCP information from the namespace
	cmd := exec.Command("nsenter", "-t", strconv.Itoa(watcher.namespacePID), "-n", "cat", "/proc/net/tcp")
	output, err := cmd.Output()
	if err != nil {
		log.Printf("Port watcher: failed to read /proc/net/tcp for namespace %s: %v", watcher.namespaceID, err)
		return
	}

	nm.parseAndNotify(strings.NewReader(string(output)), watcher, false)

	// Also scan IPv6
	cmd = exec.Command("nsenter", "-t", strconv.Itoa(watcher.namespacePID), "-n", "cat", "/proc/net/tcp6")
	output, err = cmd.Output()
	if err != nil {
		// Non-fatal - some systems might not have IPv6
		return
	}

	nm.parseAndNotify(strings.NewReader(string(output)), watcher, true)
}

// parseAndNotify parses TCP data and notifies subscribers of new ports
func (nm *NamespaceMonitor) parseAndNotify(r io.Reader, watcher *namespaceWatcher, isIPv6 bool) {
	scanner := bufio.NewScanner(r)

	// Skip header line
	if scanner.Scan() {
		// Header line, ignore
	}

	for scanner.Scan() {
		line := scanner.Text()
		fields := strings.Fields(line)

		if len(fields) < 10 {
			continue
		}

		// Parse local address (field 1)
		localAddr := fields[1]
		parts := strings.Split(localAddr, ":")
		if len(parts) != 2 {
			continue
		}

		// Parse hex address and port
		addrHex := parts[0]
		portHex := parts[1]

		// Convert port from hex
		port64, err := strconv.ParseInt(portHex, 16, 32)
		if err != nil {
			continue
		}
		port := int(port64)

		// Parse address
		var addr string
		if isIPv6 {
			if strings.HasPrefix(addrHex, "00000000000000000000000001") {
				addr = "::1"
			} else if addrHex == "00000000000000000000000000000000" {
				addr = "::"
			} else if strings.HasPrefix(addrHex, "00000000000000000000FFFF0000") {
				// IPv4-mapped IPv6 address for 0.0.0.0
				addr = "::"
			} else if addrHex == "00000000000000000000000000000001" {
				// Alternative representation of ::1
				addr = "::1"
			} else {
				// Log unrecognized IPv6 patterns for debugging
				if len(addrHex) >= 32 {
					logKey := fmt.Sprintf("%s:%d", addrHex, port)
					if !watcher.loggedAddrs[logKey] {
						watcher.loggedAddrs[logKey] = true
						log.Printf("Port watcher: skipping unrecognized IPv6 address: %s (port %d)", addrHex, port)
					}
				}
				continue
			}
		} else {
			// IPv4 address in hex (little-endian)
			addrInt, err := strconv.ParseUint(addrHex, 16, 32)
			if err != nil {
				continue
			}

			b1 := byte(addrInt & 0xFF)
			b2 := byte((addrInt >> 8) & 0xFF)
			b3 := byte((addrInt >> 16) & 0xFF)
			b4 := byte((addrInt >> 24) & 0xFF)

			addr = fmt.Sprintf("%d.%d.%d.%d", b1, b2, b3, b4)

			if addr != "127.0.0.1" && addr != "0.0.0.0" {
				continue
			}
		}

		// Parse socket inode
		inode := fields[9]

		// Find PID for this socket
		pid := findPIDForSocketFunc(inode)
		if pid == 0 {
			log.Printf("Port watcher: found listening port %s:%d but couldn't determine PID (inode: %s)\n", addr, port, inode)
			continue
		}

		// Check if this is a new port
		portKey := fmt.Sprintf("%s:%d", addr, port)
		if watcher.knownPorts[portKey] {
			continue // Already seen this port
		}
		watcher.knownPorts[portKey] = true

		// Log the new port
		log.Printf("Port watcher: new port detected in namespace %s - %s:%d (PID: %d)",
			watcher.namespaceID, addr, port, pid)

		// Notify subscribers
		nm.notifySubscribers(Port{
			Port:    port,
			PID:     pid,
			Address: addr,
		})
	}
}

// notifySubscribers notifies all relevant subscribers about a new port
func (nm *NamespaceMonitor) notifySubscribers(port Port) {
	nm.mu.RLock()
	defer nm.mu.RUnlock()

	notified := false
	// Check all subscriptions to see if this port's PID is in their tree
	for rootPID, subs := range nm.subscribers {
		if isPIDInTree(port.PID, rootPID) {
			notified = true
			for _, sub := range subs {
				// Call the callback in a goroutine to avoid blocking
				go sub.callback(port)
			}
		}
	}

	// Log when a port is detected but not in any monitored process tree
	if !notified && len(nm.subscribers) > 0 {
		log.Printf("Port watcher: detected port %s:%d (PID: %d) but it's not in any monitored process tree",
			port.Address, port.Port, port.PID)
	}
}

// getNetworkNamespace returns the network namespace inode for a PID
func getNetworkNamespace(pid int) (string, error) {
	netPath := fmt.Sprintf("/proc/%d/ns/net", pid)
	info, err := os.Readlink(netPath)
	if err != nil {
		return "", err
	}

	// Extract inode from "net:[4026531992]"
	start := strings.Index(info, "[")
	end := strings.Index(info, "]")
	if start == -1 || end == -1 {
		return "", fmt.Errorf("invalid namespace format: %s", info)
	}

	return info[start+1 : end], nil
}

// findNamespacePID1 finds PID 1 in a given network namespace
func findNamespacePID1(namespaceID string) (int, error) {
	// Read all /proc/*/status files to find NSpid
	procDir, err := os.Open("/proc")
	if err != nil {
		return 0, err
	}
	defer procDir.Close()

	entries, err := procDir.Readdir(-1)
	if err != nil {
		return 0, err
	}

	for _, entry := range entries {
		// Skip non-numeric entries
		pid, err := strconv.Atoi(entry.Name())
		if err != nil {
			continue
		}

		// Check if this PID is in our target namespace
		pidNamespace, err := getNetworkNamespace(pid)
		if err != nil {
			continue
		}

		if pidNamespace != namespaceID {
			continue
		}

		// Check if this is PID 1 in the namespace
		statusPath := filepath.Join("/proc", entry.Name(), "status")
		data, err := os.ReadFile(statusPath)
		if err != nil {
			continue
		}

		// Look for NSpid line
		lines := strings.Split(string(data), "\n")
		for _, line := range lines {
			if strings.HasPrefix(line, "NSpid:") {
				fields := strings.Fields(line)
				if len(fields) >= 2 && fields[len(fields)-1] == "1" {
					return pid, nil
				}
			}
		}
	}

	return 0, fmt.Errorf("could not find PID 1 for namespace %s", namespaceID)
}

// getNamedNamespaceID returns the inode ID of a named network namespace
func getNamedNamespaceID(name string) (string, error) {
	nsPath := fmt.Sprintf("/var/run/netns/%s", name)
	info, err := os.Stat(nsPath)
	if err != nil {
		return "", fmt.Errorf("namespace %s not found: %w", name, err)
	}

	// Get the inode number
	stat, ok := info.Sys().(*syscall.Stat_t)
	if !ok {
		return "", fmt.Errorf("failed to get stat info for namespace %s", name)
	}

	return strconv.FormatUint(stat.Ino, 10), nil
}

// Helper functions (these should be shared with the original implementation)

// findPIDForSocketFunc is a variable to allow mocking in tests
var findPIDForSocketFunc = findPIDForSocket

func findPIDForSocket(inode string) int {
	procDir, err := os.Open("/proc")
	if err != nil {
		return 0
	}
	defer procDir.Close()

	entries, err := procDir.Readdir(-1)
	if err != nil {
		return 0
	}

	socketPath := fmt.Sprintf("socket:[%s]", inode)

	for _, entry := range entries {
		pid, err := strconv.Atoi(entry.Name())
		if err != nil {
			continue
		}

		fdPath := filepath.Join("/proc", entry.Name(), "fd")
		fdDir, err := os.Open(fdPath)
		if err != nil {
			continue
		}

		fdEntries, err := fdDir.Readdir(-1)
		fdDir.Close()
		if err != nil {
			continue
		}

		for _, fdEntry := range fdEntries {
			linkPath := filepath.Join(fdPath, fdEntry.Name())
			link, err := os.Readlink(linkPath)
			if err != nil {
				continue
			}

			if link == socketPath {
				return pid
			}
		}
	}

	return 0
}

func isPIDInTree(pid int, rootPID int) bool {
	if pid == rootPID {
		return true
	}

	currentPID := pid
	for currentPID != 0 && currentPID != 1 {
		ppid := getParentPID(currentPID)
		if ppid == rootPID {
			return true
		}
		currentPID = ppid
	}

	return false
}

func getParentPID(pid int) int {
	statPath := fmt.Sprintf("/proc/%d/stat", pid)
	data, err := os.ReadFile(statPath)
	if err != nil {
		return 0
	}

	content := string(data)
	lastParen := strings.LastIndex(content, ")")
	if lastParen == -1 {
		return 0
	}

	fields := strings.Fields(content[lastParen+1:])
	if len(fields) < 2 {
		return 0
	}

	ppid, err := strconv.Atoi(fields[1])
	if err != nil {
		return 0
	}

	return ppid
}
