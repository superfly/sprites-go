// Package portwatcher monitors when a process or its children start listening on ports bound to localhost or all interfaces
package portwatcher

import (
	"fmt"
	"log"
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
// It now uses the global namespace monitor for efficiency
type PortWatcher struct {
	pid      int
	callback PortCallback
	monitor  *NamespaceMonitor
}

// New creates a new PortWatcher for the given PID
func New(pid int, callback PortCallback) (*PortWatcher, error) {
	pw := &PortWatcher{
		pid:      pid,
		callback: callback,
		monitor:  GetGlobalMonitor(),
	}

	log.Printf("Port watcher: creating watcher for PID %d\n", pid)

	return pw, nil
}

// Start begins monitoring for new ports
func (pw *PortWatcher) Start() error {
	// Subscribe to the global namespace monitor
	if err := pw.monitor.Subscribe(pw.pid, pw.callback); err != nil {
		return fmt.Errorf("failed to subscribe to namespace monitor: %w", err)
	}
	return nil
}

// Stop stops the port watcher
func (pw *PortWatcher) Stop() {
	// Unsubscribe from the global namespace monitor
	pw.monitor.Unsubscribe(pw.pid)
}
