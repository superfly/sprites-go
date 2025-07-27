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
	currentPorts map[string]int  // key: "addr:port" value: PID
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
			currentPorts: make(map[string]int),
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
	// Collect all seen ports from both IPv4 and IPv6
	allSeenPorts := make(map[string]int)

	// Use nsenter to read TCP information from the namespace
	cmd := exec.Command("nsenter", "-t", strconv.Itoa(watcher.namespacePID), "-n", "cat", "/proc/net/tcp")
	output, err := cmd.Output()
	if err != nil {
		log.Printf("Port watcher: failed to read /proc/net/tcp for namespace %s: %v", watcher.namespaceID, err)
		return
	}

	ipv4Ports := nm.parseAndNotify(strings.NewReader(string(output)), watcher, false)
	// Merge IPv4 ports into allSeenPorts
	for k, v := range ipv4Ports {
		allSeenPorts[k] = v
	}

	// Also scan IPv6
	cmd = exec.Command("nsenter", "-t", strconv.Itoa(watcher.namespacePID), "-n", "cat", "/proc/net/tcp6")
	output, err = cmd.Output()
	if err != nil {
		// Non-fatal - some systems might not have IPv6
		log.Printf("Port watcher: failed to read /proc/net/tcp6 for namespace %s: %v", watcher.namespaceID, err)
	} else {
		ipv6Ports := nm.parseAndNotify(strings.NewReader(string(output)), watcher, true)
		// Merge IPv6 ports into allSeenPorts
		for k, v := range ipv6Ports {
			allSeenPorts[k] = v
		}
	}

	// Debug: log current state
	if len(watcher.currentPorts) > 0 || len(allSeenPorts) > 0 {
		log.Printf("Port watcher DEBUG: namespace %s - before: %d ports, after scan: %d ports",
			watcher.namespaceID, len(watcher.currentPorts), len(allSeenPorts))
	}

	// Now update currentPorts based on ALL seen ports
	// Remove ports that are no longer present
	for portKey := range watcher.currentPorts {
		if _, stillExists := allSeenPorts[portKey]; !stillExists {
			// Port was closed - notify subscribers
			parts := strings.Split(portKey, ":")
			if len(parts) >= 2 {
				// For IPv6, we might have multiple colons, so take the last part
				portStr := parts[len(parts)-1]
				port, _ := strconv.Atoi(portStr)
				// Reconstruct address by joining all parts except the last
				addr := strings.Join(parts[:len(parts)-1], ":")

				pid := watcher.currentPorts[portKey]
				// Check if anyone cares about this closed port
				inMonitoredTree := false
				nm.mu.RLock()
				for rootPID := range nm.subscribers {
					if isPIDInTree(pid, rootPID) {
						inMonitoredTree = true
						break
					}
				}
				nm.mu.RUnlock()

				// Always log port closures for debugging
				log.Printf("Port watcher: detected closed port in namespace %s - %s (PID: %d, monitored: %v)",
					watcher.namespaceID, portKey, pid, inMonitoredTree)

				// Notify subscribers
				nm.notifySubscribers(Port{
					Port:    port,
					PID:     pid,
					Address: addr,
					State:   "closed",
				})
			}
			delete(watcher.currentPorts, portKey)
		}
	}

	// Add new ports
	for portKey, pid := range allSeenPorts {
		if watcher.currentPorts[portKey] == 0 {
			// This is handled in parseAndNotify already
		}
		watcher.currentPorts[portKey] = pid
	}
}

// parseAndNotify parses TCP data and notifies subscribers
func (nm *NamespaceMonitor) parseAndNotify(r io.Reader, watcher *namespaceWatcher, isIPv6 bool) map[string]int {
	scanner := bufio.NewScanner(r)

	// Track ports seen in this scan
	seenPorts := make(map[string]int) // key: "addr:port" value: PID

	// Skip header line
	if scanner.Scan() {
		// Process data lines
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
							readableAddr := hexToIPv6(addrHex)
							log.Printf("Port watcher: skipping unrecognized IPv6 address: %s (port %d)", readableAddr, port)
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

			// Track this port as seen
			portKey := fmt.Sprintf("%s:%d", addr, port)
			if seenPorts[portKey] != 0 {
				continue // Already seen in this scan
			}
			seenPorts[portKey] = pid

			// Check if this is a new port
			if watcher.currentPorts[portKey] == 0 {
				// New port opened - check if anyone cares about it
				inMonitoredTree := false
				nm.mu.RLock()
				for rootPID := range nm.subscribers {
					if isPIDInTree(pid, rootPID) {
						inMonitoredTree = true
						break
					}
				}
				nm.mu.RUnlock()

				if inMonitoredTree {
					log.Printf("Port watcher: new port detected in namespace %s - %s:%d (PID: %d)",
						watcher.namespaceID, addr, port, pid)
				}

				// Notify subscribers (only those whose tree contains this PID)
				nm.notifySubscribers(Port{
					Port:    port,
					PID:     pid,
					Address: addr,
					State:   "open",
				})
			}
		}
	}

	return seenPorts
}

// notifySubscribers notifies all relevant subscribers about a new port
func (nm *NamespaceMonitor) notifySubscribers(port Port) {
	nm.mu.RLock()
	defer nm.mu.RUnlock()

	// Check all subscriptions to see if this port's PID is in their tree
	for rootPID, subs := range nm.subscribers {
		shouldNotify := false

		if port.State == "closed" {
			// For closed ports, the process might have already exited
			// So we can't reliably check if it's in the tree
			// Instead, notify if this subscriber was monitoring anything in this namespace
			// (they likely got the open event and need the close event)
			shouldNotify = true
		} else {
			// For open ports, check if the PID is in the subscriber's tree
			shouldNotify = isPIDInTree(port.PID, rootPID)
		}

		if shouldNotify {
			for _, sub := range subs {
				// Call the callback in a goroutine to avoid blocking
				go sub.callback(port)
			}
		}
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

// hexToIPv6 converts a hex string to IPv6 address format
func hexToIPv6(hex string) string {
	if len(hex) != 32 {
		return hex // Return as-is if not valid length
	}

	// Convert to IPv6 format (e.g., "2001:0db8:0000:0000:0000:0000:0000:0001")
	var parts []string
	for i := 0; i < 32; i += 4 {
		part := strings.ToLower(hex[i : i+4])
		parts = append(parts, part)
	}

	// Join with colons
	return strings.Join(parts, ":")
}

// findPIDForSocket scans /proc/*/fd/* to find which process owns a socket
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
