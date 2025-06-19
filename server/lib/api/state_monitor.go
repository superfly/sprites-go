package api

import (
	"context"
	"sync"

	"sprite-env/lib"
)

// APIStateMonitor monitors system state transitions and provides a way to wait for
// the system to be ready to handle requests
type APIStateMonitor struct {
	mu           sync.RWMutex
	currentState string
	waiters      []chan struct{}
	events       chan lib.StateTransition
	done         chan struct{}
	wg           sync.WaitGroup
}

// NewAPIStateMonitor creates a new API state monitor
func NewAPIStateMonitor() *APIStateMonitor {
	monitor := &APIStateMonitor{
		currentState: "Initializing",
		waiters:      make([]chan struct{}, 0),
		events:       make(chan lib.StateTransition, 100),
		done:         make(chan struct{}),
	}

	// Start processing events
	monitor.wg.Add(1)
	go monitor.processEvents()

	return monitor
}

// Events implements StateMonitor interface
func (m *APIStateMonitor) Events() chan<- lib.StateTransition {
	return m.events
}

// WaitForReady waits for the system to be in a state where it can handle requests.
// It returns immediately if the system is already ready.
// It waits if the system is starting up or restoring.
func (m *APIStateMonitor) WaitForReady(ctx context.Context) error {
	m.mu.RLock()
	if m.isReadyState(m.currentState) {
		m.mu.RUnlock()
		return nil
	}
	m.mu.RUnlock()

	// Create a channel to wait on
	waiter := make(chan struct{})

	m.mu.Lock()
	// Check again with write lock
	if m.isReadyState(m.currentState) {
		m.mu.Unlock()
		return nil
	}
	m.waiters = append(m.waiters, waiter)
	m.mu.Unlock()

	// Wait for ready state or context cancellation
	select {
	case <-waiter:
		return nil
	case <-ctx.Done():
		// Remove our waiter
		m.mu.Lock()
		for i, w := range m.waiters {
			if w == waiter {
				m.waiters = append(m.waiters[:i], m.waiters[i+1:]...)
				break
			}
		}
		m.mu.Unlock()
		return ctx.Err()
	}
}

// processEvents processes state transition events
func (m *APIStateMonitor) processEvents() {
	defer m.wg.Done()

	for {
		select {
		case transition := <-m.events:
			// Only care about SystemState transitions
			if transition.Name != "SystemState" {
				continue
			}

			m.mu.Lock()
			oldState := m.currentState
			m.currentState = transition.To

			// Check if we transitioned to a ready state
			if !m.isReadyState(oldState) && m.isReadyState(transition.To) {
				// Notify all waiters
				for _, waiter := range m.waiters {
					close(waiter)
				}
				m.waiters = make([]chan struct{}, 0)
			} else if m.isReadyState(oldState) && !m.isReadyState(transition.To) {
				// We transitioned away from ready (e.g., started restoring)
				// New waiters will need to wait
			}
			m.mu.Unlock()

		case <-m.done:
			// Shutdown requested - notify any remaining waiters
			m.mu.Lock()
			for _, waiter := range m.waiters {
				close(waiter)
			}
			m.waiters = nil
			m.mu.Unlock()
			return
		}
	}
}

// isReadyState returns true if the state allows handling requests
func (m *APIStateMonitor) isReadyState(state string) bool {
	switch state {
	case "Running":
		// System is fully operational
		return true
	case "Checkpointing":
		// Allow requests during checkpointing
		return true
	case "Initializing", "Starting", "Ready", "Restoring":
		// Don't handle requests during these states
		return false
	case "ErrorRecovery", "Stopping", "Error", "Stopped":
		// Terminal or error states - don't wait, let requests fail immediately
		return true
	default:
		// Unknown state - be conservative and wait
		return false
	}
}

// Close stops the monitor
func (m *APIStateMonitor) Close() error {
	select {
	case <-m.done:
		// Already closed
		return nil
	default:
		close(m.done)
		m.wg.Wait()
		return nil
	}
}
