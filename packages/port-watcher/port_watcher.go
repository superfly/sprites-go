// Package portwatcher monitors when a process or its children start listening on ports bound to localhost or all interfaces
package portwatcher

import (
	"bufio"
	"context"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"time"

	"github.com/fsnotify/fsnotify"
)

// Port represents a listening port
type Port struct {
	Port    int
	PID     int
	Address string
}

// PortCallback is called when a new port is detected
type PortCallback func(port Port)

// portEvent is used internally for channel communication
type portEvent struct {
	portKey string
	port    Port
}

// PortWatcher monitors ports for a process and its children
type PortWatcher struct {
	pid              int
	callback         PortCallback
	watcher          *fsnotify.Watcher
	ctx              context.Context
	cancel           context.CancelFunc
	wg               sync.WaitGroup
	portEventChan    chan portEvent
	knownPortsChan   chan map[string]bool
	findPIDForSocket func(inode string) int // Made this a function field for testing
}

// New creates a new PortWatcher for the given PID
func New(pid int, callback PortCallback) (*PortWatcher, error) {
	watcher, err := fsnotify.NewWatcher()
	if err != nil {
		return nil, fmt.Errorf("failed to create fsnotify watcher: %w", err)
	}

	ctx, cancel := context.WithCancel(context.Background())

	pw := &PortWatcher{
		pid:            pid,
		callback:       callback,
		watcher:        watcher,
		ctx:            ctx,
		cancel:         cancel,
		portEventChan:  make(chan portEvent, 100),
		knownPortsChan: make(chan map[string]bool, 1),
	}

	// Initialize known ports map through channel
	pw.knownPortsChan <- make(map[string]bool)

	// Set the default findPIDForSocket function
	pw.findPIDForSocket = pw.defaultFindPIDForSocket

	// Add /proc/net/tcp to watch list
	if err := watcher.Add("/proc/net/tcp"); err != nil {
		watcher.Close()
		return nil, fmt.Errorf("failed to watch /proc/net/tcp: %w", err)
	}

	// Also watch /proc/net/tcp6 for IPv6
	if err := watcher.Add("/proc/net/tcp6"); err != nil {
		// Non-fatal, some systems might not have IPv6
		// Just log or ignore
	}

	return pw, nil
}

// Start begins monitoring for new ports
func (pw *PortWatcher) Start() error {
	// Start the port event processor
	pw.wg.Add(1)
	go pw.processPortEvents()

	// Do an initial scan
	if err := pw.scanPorts(); err != nil {
		return fmt.Errorf("initial port scan failed: %w", err)
	}

	pw.wg.Add(1)
	go pw.watchLoop()

	return nil
}

// Stop stops the port watcher
func (pw *PortWatcher) Stop() {
	pw.cancel()
	pw.watcher.Close()
	close(pw.portEventChan)
	pw.wg.Wait()
}

func (pw *PortWatcher) processPortEvents() {
	defer pw.wg.Done()

	for {
		select {
		case <-pw.ctx.Done():
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
			case <-pw.ctx.Done():
				return
			}
		}
	}
}

func (pw *PortWatcher) watchLoop() {
	defer pw.wg.Done()

	// Use a ticker for periodic scans as fsnotify might not catch all changes
	ticker := time.NewTicker(1 * time.Second)
	defer ticker.Stop()

	for {
		select {
		case <-pw.ctx.Done():
			return
		case event, ok := <-pw.watcher.Events:
			if !ok {
				return
			}
			// Only scan on write events
			if event.Op&fsnotify.Write == fsnotify.Write {
				pw.scanPorts()
			}
		case err, ok := <-pw.watcher.Errors:
			if !ok {
				return
			}
			// Log error but continue
			_ = err
		case <-ticker.C:
			// Periodic scan as backup
			pw.scanPorts()
		}
	}
}

func (pw *PortWatcher) scanPorts() error {
	// Scan /proc/net/tcp
	if err := pw.scanTCPFile("/proc/net/tcp", false); err != nil {
		return err
	}

	// Scan /proc/net/tcp6
	if err := pw.scanTCPFile("/proc/net/tcp6", true); err != nil {
		// Non-fatal for IPv6
	}

	return nil
}

func (pw *PortWatcher) scanTCPFile(path string, isIPv6 bool) error {
	file, err := os.Open(path)
	if err != nil {
		return err
	}
	defer file.Close()

	return pw.parseTCPFile(file, isIPv6)
}

func (pw *PortWatcher) parseTCPFile(r io.Reader, isIPv6 bool) error {
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

		// Parse hex address
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
			// For IPv6, handle localhost (::1) and all interfaces (::)
			if strings.HasPrefix(addrHex, "00000000000000000000000001") {
				addr = "::1"
			} else if addrHex == "00000000000000000000000000000000" {
				addr = "::"
			} else {
				continue // Not localhost or all interfaces
			}
		} else {
			// IPv4 address in hex (little-endian)
			addrInt, err := strconv.ParseUint(addrHex, 16, 32)
			if err != nil {
				continue
			}

			// Convert to IP address
			b1 := byte(addrInt & 0xFF)
			b2 := byte((addrInt >> 8) & 0xFF)
			b3 := byte((addrInt >> 16) & 0xFF)
			b4 := byte((addrInt >> 24) & 0xFF)

			addr = fmt.Sprintf("%d.%d.%d.%d", b1, b2, b3, b4)

			// Accept localhost (127.0.0.1) and all interfaces (0.0.0.0)
			if addr != "127.0.0.1" && addr != "0.0.0.0" {
				continue
			}
		}

		// Parse socket inode (field 9)
		inode := fields[9]

		// Find PID for this socket
		pid := pw.findPIDForSocket(inode)
		if pid == 0 {
			continue
		}

		// Check if this PID is in our process tree
		if !pw.isPIDInTree(pid) {
			continue
		}

		// Send port event for processing
		portKey := fmt.Sprintf("%s:%d:%d", addr, port, pid)

		select {
		case pw.portEventChan <- portEvent{
			portKey: portKey,
			port: Port{
				Port:    port,
				PID:     pid,
				Address: addr,
			},
		}:
		case <-pw.ctx.Done():
			return nil
		default:
			// Channel full, skip this port
		}
	}

	return scanner.Err()
}

func (pw *PortWatcher) defaultFindPIDForSocket(inode string) int {
	// Scan /proc/*/fd/* to find which process owns this socket
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
		// Skip non-numeric entries (not PIDs)
		pid, err := strconv.Atoi(entry.Name())
		if err != nil {
			continue
		}

		// Check fd directory
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

func (pw *PortWatcher) isPIDInTree(pid int) bool {
	// Check if this PID is our target PID or one of its children
	if pid == pw.pid {
		return true
	}

	// Walk up the process tree to see if we find our target PID
	currentPID := pid
	for currentPID != 0 && currentPID != 1 {
		ppid := pw.getParentPID(currentPID)
		if ppid == pw.pid {
			return true
		}
		currentPID = ppid
	}

	return false
}

func (pw *PortWatcher) getParentPID(pid int) int {
	statPath := fmt.Sprintf("/proc/%d/stat", pid)
	data, err := os.ReadFile(statPath)
	if err != nil {
		return 0
	}

	// The format is: pid (comm) state ppid ...
	// We need to find the closing ) and then parse ppid
	content := string(data)

	// Find the last ) to handle commands with ) in their name
	lastParen := strings.LastIndex(content, ")")
	if lastParen == -1 {
		return 0
	}

	// Fields after the command name
	fields := strings.Fields(content[lastParen+1:])
	if len(fields) < 2 {
		return 0
	}

	// ppid is the second field after the command
	ppid, err := strconv.Atoi(fields[1])
	if err != nil {
		return 0
	}

	return ppid
}
