// Package portwatcher monitors when a process or its children start listening on ports bound to localhost or all interfaces
package portwatcher

import (
	"fmt"
	"log"
	"time"

	"github.com/superfly/sprite-env/packages/container"
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
	// Wait a bit for the container process to spawn
	time.Sleep(50 * time.Millisecond)

	// Try to find the actual container process PID
	wrapperPID := pid
	containerPID := wrapperPID // Default to wrapper PID if we can't find child

	if childPID, err := container.GetContainerPID(wrapperPID); err == nil {
		containerPID = childPID
		log.Printf("Port watcher: found container child process - wrapperPID: %d, containerPID: %d\n", wrapperPID, containerPID)
	} else {
		log.Printf("Port watcher: could not find container child process, using wrapper PID - wrapperPID: %d, error: %v\n", wrapperPID, err)
	}

	pw := &PortWatcher{
		pid:      containerPID,
		callback: callback,
		monitor:  GetGlobalMonitor(),
	}

	log.Printf("Port watcher: creating watcher for PID %d\n", containerPID)

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
