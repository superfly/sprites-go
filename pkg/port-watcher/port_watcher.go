// Package portwatcher monitors when a process or its children start listening on ports bound to localhost or all interfaces
package portwatcher

import (
	"fmt"
	"log"
	"sync"
)

// Port represents a listening port
type Port struct {
	Port    int
	PID     int
	Address string
	State   string // "open" or "closed"
}

// PortCallback is called when a port state changes
type PortCallback func(port Port)

// PortWatcher monitors ports for a process and its children
// It now uses the global namespace monitor for efficiency
type PortWatcher struct {
	mu        sync.Mutex
	pids      []int  // List of PIDs being monitored
	namespace string // Network namespace name (required, e.g., "sprite")
	callback  PortCallback
	monitor   *NamespaceMonitor
	idle      bool // true if this is an idle instance that does nothing
}

// New creates a new PortWatcher for the given PID
func New(pid int, namespace string, callback PortCallback) (*PortWatcher, error) {
	if namespace == "" {
		return nil, fmt.Errorf("namespace name is required")
	}

	pw := &PortWatcher{
		pids:      []int{pid},
		namespace: namespace,
		callback:  callback,
		monitor:   GetGlobalMonitor(),
	}

	log.Printf("Port watcher: creating watcher for PID %d in namespace %s\n", pid, namespace)

	return pw, nil
}

// Start begins monitoring for new ports
func (pw *PortWatcher) Start() error {
	pw.mu.Lock()
	defer pw.mu.Unlock()

	// If this is an idle instance, do nothing
	if pw.idle {
		return nil
	}

	// Subscribe all PIDs to the global namespace monitor
	for _, pid := range pw.pids {
		if err := pw.monitor.SubscribeInNamespace(pid, pw.namespace, pw.callback); err != nil {
			log.Printf("Port watcher: failed to subscribe PID %d: %v\n", pid, err)
			// Continue with other PIDs even if one fails
		}
	}

	// If we couldn't subscribe any PIDs, mark as idle
	if len(pw.pids) == 0 {
		pw.idle = true
	}

	return nil
}

// Stop stops the port watcher
func (pw *PortWatcher) Stop() {
	pw.mu.Lock()
	defer pw.mu.Unlock()

	// If this is an idle instance, do nothing
	if pw.idle {
		return
	}

	// Unsubscribe all PIDs from the global namespace monitor
	for _, pid := range pw.pids {
		pw.monitor.Unsubscribe(pid)
	}
}

// AddPID adds a new PID to monitor
func (pw *PortWatcher) AddPID(pid int) error {
	pw.mu.Lock()
	defer pw.mu.Unlock()

	// Check if PID is already being monitored
	for _, existingPID := range pw.pids {
		if existingPID == pid {
			return nil // Already monitoring this PID
		}
	}

	log.Printf("Port watcher: adding PID %d to monitoring\n", pid)

	// Subscribe the new PID
	if err := pw.monitor.SubscribeInNamespace(pid, pw.namespace, pw.callback); err != nil {
		return err
	}

	// Add to our list
	pw.pids = append(pw.pids, pid)

	// If we were idle, we're not anymore
	pw.idle = false

	return nil
}

// RemovePID removes a PID from monitoring
func (pw *PortWatcher) RemovePID(pid int) {
	pw.mu.Lock()
	defer pw.mu.Unlock()

	// Find and remove the PID
	for i, existingPID := range pw.pids {
		if existingPID == pid {
			log.Printf("Port watcher: removing PID %d from monitoring\n", pid)

			// Unsubscribe from monitor
			pw.monitor.Unsubscribe(pid)

			// Remove from slice
			pw.pids = append(pw.pids[:i], pw.pids[i+1:]...)

			// If no more PIDs, mark as idle
			if len(pw.pids) == 0 {
				pw.idle = true
			}

			return
		}
	}
}
