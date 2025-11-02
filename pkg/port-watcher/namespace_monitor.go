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
	tickerCancel context.CancelFunc // Separate cancel for ticker goroutine
}

// namespaceWatcher monitors a specific network namespace
type namespaceWatcher struct {
	namespaceID  string          // Same as namespace name for named namespaces
	namespace    string          // Network namespace name (e.g., "sprite")
	currentPorts map[string]int  // key: "addr:port" value: PID
	loggedAddrs  map[string]bool // key: "addr:port" for unrecognized addresses
}

// subscription represents a subscription to port events for a PID tree
type subscription struct {
	rootPID   int
	namespace string // Network namespace name (e.g., "sprite")
	callback  PortCallback
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
		// Don't start the ticker automatically - wait for subscriptions
	})
	return globalMonitor
}

// SubscribeInNamespace subscribes to port events for a PID and its children within a specific namespace
func (nm *NamespaceMonitor) SubscribeInNamespace(pid int, namespace string, callback PortCallback) error {
	// Require namespace
	if namespace == "" {
		return fmt.Errorf("namespace name is required for monitoring")
	}

	// Lock for the data structure updates
	nm.mu.Lock()
	defer nm.mu.Unlock()

	// Find or create the namespace watcher
	if _, exists := nm.monitors[namespace]; !exists {
		// Create a new namespace watcher
		nm.monitors[namespace] = &namespaceWatcher{
			namespaceID:  namespace,
			namespace:    namespace,
			currentPorts: make(map[string]int),
			loggedAddrs:  make(map[string]bool),
		}
		// quiet: no log here
	}

	// Add the subscription
	sub := &subscription{
		rootPID:   pid,
		namespace: namespace,
		callback:  callback,
	}
	nm.subscribers[pid] = append(nm.subscribers[pid], sub)

	log.Printf("Port watcher: subscribed to PID %d in namespace %s (will monitor this PID and its children)", pid, namespace)

	// Immediately notify about any ports that are already open for this PID
	// Check the namespace watcher's currentPorts map
	watcher := nm.monitors[namespace]
	for portKey, portPID := range watcher.currentPorts {
		// Check if this port belongs to the subscribed PID or its children
		if isPIDInTree(portPID, pid) {
			// Parse the portKey "addr:port" to extract address and port
			parts := strings.Split(portKey, ":")
			if len(parts) >= 2 {
				portStr := parts[len(parts)-1]
				port, err := strconv.Atoi(portStr)
				if err == nil {
					addr := strings.Join(parts[:len(parts)-1], ":")
					// Send open event in a goroutine to avoid blocking
					go callback(Port{
						Port:    port,
						PID:     portPID,
						Address: addr,
						State:   "open",
					})
				}
			}
		}
	}

	// Start ticker if this is the first subscription
	if nm.tickerCancel == nil {
		tickerCtx, tickerCancel := context.WithCancel(context.Background())
		nm.tickerCancel = tickerCancel
		go nm.run(tickerCtx)
	}

	return nil
}

// Unsubscribe removes a subscription for a PID
func (nm *NamespaceMonitor) Unsubscribe(pid int) {
	nm.mu.Lock()
	defer nm.mu.Unlock()

	delete(nm.subscribers, pid)

	// Stop ticker if no more subscribers
	if len(nm.subscribers) == 0 && nm.tickerCancel != nil {
		nm.tickerCancel()
		nm.tickerCancel = nil
		// quiet: no log here

		// Clean up all namespace watchers
		nm.monitors = make(map[string]*namespaceWatcher)
	}
}

// Stop stops the global monitor
func (nm *NamespaceMonitor) Stop() {
	nm.cancel()
}

// run is the main loop for the namespace monitor
func (nm *NamespaceMonitor) run(ctx context.Context) {
	ticker := time.NewTicker(nm.pollInterval)
	defer ticker.Stop()

	for {
		select {
		case <-ctx.Done():
			return
		case <-ticker.C:
			nm.scanAllNamespaces()
		}
	}
}

// scanAllNamespaces scans all monitored namespaces
func (nm *NamespaceMonitor) scanAllNamespaces() {
	nm.mu.RLock()
	watchers := make(map[string]*namespaceWatcher)
	for id, watcher := range nm.monitors {
		watchers[id] = watcher
	}
	nm.mu.RUnlock()

	for _, watcher := range watchers {
		nm.scanNamespace(watcher)
	}
}

// scanNamespace scans for new ports in a namespace
func (nm *NamespaceMonitor) scanNamespace(watcher *namespaceWatcher) {
	// Use the named network namespace
	if watcher.namespace == "" {
		return
	}
	cmd := exec.Command("nsenter", "--net=/var/run/netns/"+watcher.namespace, "ss", "-ltnp")
	output, err := cmd.Output()
	if err != nil {
		return
	}
	allSeenPorts := nm.parseSSOutput(string(output), watcher)

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

				// Log port closure
				log.Printf("Port watcher: port closed in namespace %s - %s (PID: %d)",
					watcher.namespaceID, portKey, pid)

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
				} else if strings.HasPrefix(addrHex, "0FDF0000000000000000000000000001") {
					// fdf::1 (sprite container address)
					addr = "fdf::1"
				} else {
					// Quiet: ignore unrecognized IPv6 patterns
					if len(addrHex) >= 32 {
						logKey := fmt.Sprintf("%s:%d", addrHex, port)
						if !watcher.loggedAddrs[logKey] {
							watcher.loggedAddrs[logKey] = true
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
				// New port opened
				log.Printf("Port watcher: new port detected in namespace %s - %s:%d (PID: %d)",
					watcher.namespaceID, addr, port, pid)

				// Notify subscribers
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

// parseSSOutput parses ss command output and returns seen ports
func (nm *NamespaceMonitor) parseSSOutput(output string, watcher *namespaceWatcher) map[string]int {
	seenPorts := make(map[string]int)

	lines := strings.Split(output, "\n")
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if line == "" || !strings.HasPrefix(line, "LISTEN") {
			continue
		}

		// Parse ss output format: State Recv-Q Send-Q Local-Address:Port Peer-Address:Port Process
		fields := strings.Fields(line)
		if len(fields) < 6 {
			continue
		}

		localAddr := fields[3]   // Local Address:Port
		processInfo := fields[5] // Process info like users:(("claude",pid=9506,fd=29))

		// Extract address and port
		// Handle IPv6 addresses with brackets like [::1]:46061
		var addr string
		var portStr string

		if strings.HasPrefix(localAddr, "[") {
			// IPv6 format: [addr]:port
			closeBracket := strings.LastIndex(localAddr, "]")
			if closeBracket == -1 || closeBracket+1 >= len(localAddr) || localAddr[closeBracket+1] != ':' {
				continue
			}
			addr = localAddr[1:closeBracket] // Remove brackets
			portStr = localAddr[closeBracket+2:]
		} else {
			// IPv4 format: addr:port
			lastColon := strings.LastIndex(localAddr, ":")
			if lastColon == -1 {
				continue
			}
			addr = localAddr[:lastColon]
			portStr = localAddr[lastColon+1:]
		}

		port, err := strconv.Atoi(portStr)
		if err != nil {
			continue
		}

		// Normalize addresses we care about
		var normalizedAddr string
		switch addr {
		case "*", "0.0.0.0":
			normalizedAddr = "0.0.0.0"
		case "127.0.0.1":
			normalizedAddr = "127.0.0.1"
		case "::":
			normalizedAddr = "::"
		case "::1":
			normalizedAddr = "::1"
		case "fdf::1":
			normalizedAddr = "fdf::1"
		default:
			// Skip addresses we don't monitor
			continue
		}

		// Extract PID from process info: users:(("claude",pid=9506,fd=29))
		pid := nm.extractPIDFromProcessInfo(processInfo)
		if pid == 0 {
			continue
		}

		portKey := fmt.Sprintf("%s:%d", normalizedAddr, port)

		if seenPorts[portKey] != 0 {
			continue // Already seen
		}
		seenPorts[portKey] = pid

		// Check if this is a new port
		if watcher.currentPorts[portKey] == 0 {
			// New port opened
			log.Printf("Port watcher: new port detected in namespace %s - %s:%d (PID: %d)",
				watcher.namespaceID, normalizedAddr, port, pid)

			// Notify subscribers
			nm.notifySubscribers(Port{
				Port:    port,
				PID:     pid,
				Address: normalizedAddr,
				State:   "open",
			})
		}
	}

	return seenPorts
}

// extractPIDFromProcessInfo extracts PID from ss process info like users:(("claude",pid=9506,fd=29))
func (nm *NamespaceMonitor) extractPIDFromProcessInfo(processInfo string) int {
	// Find "pid=" pattern
	pidStart := strings.Index(processInfo, "pid=")
	if pidStart == -1 {
		return 0
	}

	pidStart += 4 // Skip "pid="
	pidEnd := strings.IndexAny(processInfo[pidStart:], ",)")
	if pidEnd == -1 {
		return 0
	}

	pidStr := processInfo[pidStart : pidStart+pidEnd]
	pid, err := strconv.Atoi(pidStr)
	if err != nil {
		return 0
	}

	return pid
}

// notifySubscribers notifies all relevant subscribers about a port change
func (nm *NamespaceMonitor) notifySubscribers(port Port) {
	nm.mu.RLock()
	defer nm.mu.RUnlock()

	// Check all subscriptions to see if this port's PID is in their tree
	notifiedCount := 0
	for rootPID, subs := range nm.subscribers {
		isInTree := isPIDInTree(port.PID, rootPID)
		if isInTree {
			for _, sub := range subs {
				notifiedCount++
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

// debugPrintProcessTree prints the full process tree for a PID
func (nm *NamespaceMonitor) debugPrintProcessTree(pid int) {
	log.Printf("Port watcher: Process tree for PID %d:", pid)

	// Build the tree
	currentPID := pid
	tree := []string{}

	for currentPID != 0 && currentPID != 1 {
		// Get process name
		cmdPath := fmt.Sprintf("/proc/%d/comm", currentPID)
		cmdBytes, _ := os.ReadFile(cmdPath)
		cmd := strings.TrimSpace(string(cmdBytes))
		if cmd == "" {
			cmd = "?"
		}

		// Get parent PID
		ppid := getParentPID(currentPID)

		tree = append(tree, fmt.Sprintf("  %d (%s) -> parent: %d", currentPID, cmd, ppid))
		currentPID = ppid
	}

	// Print tree
	for _, line := range tree {
		log.Print(line)
	}

	// Also print command line for the original PID
	cmdlinePath := fmt.Sprintf("/proc/%d/cmdline", pid)
	if cmdlineBytes, err := os.ReadFile(cmdlinePath); err == nil {
		cmdline := strings.ReplaceAll(string(cmdlineBytes), "\x00", " ")
		log.Printf("  Command line: %s", strings.TrimSpace(cmdline))
	}
}

func isPIDInTree(pid int, rootPID int) bool {
	if pid == rootPID {
		return true
	}

	currentPID := pid
	pidPath := []int{currentPID}
	for currentPID != 0 && currentPID != 1 {
		ppid := getParentPID(currentPID)
		pidPath = append(pidPath, ppid)
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
