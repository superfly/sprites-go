package managers

import (
	"context"
	"io"
	"sync"
	"time"

	"github.com/qmuntal/stateless"
)

// StateTransition represents a state change event
type StateTransition struct {
	Name    string
	From    string
	To      string
	Trigger string
}

// StateMonitor defines the interface for monitoring state transitions
type StateMonitor interface {
	Events() chan<- StateTransition
}

// StateMonitorFunc is a function type for outputting trace events
type StateMonitorFunc func(StateTransition)

// stateMonitor provides a simple implementation of StateMonitor with graceful shutdown
type stateMonitor struct {
	events   chan StateTransition // Buffered channel - handles burst patterns during startup/shutdown
	done     chan struct{}        // Unbuffered - used for signaling via close()
	outputFn StateMonitorFunc
	wg       sync.WaitGroup // Tracks the processEvents goroutine
}

// NewStateMonitor creates a new state monitor with the given output function
func NewStateMonitor(outputFn StateMonitorFunc) StateMonitor {
	monitor := &stateMonitor{
		events:   make(chan StateTransition, 100), // Buffered channel - handles burst patterns during startup/shutdown
		done:     make(chan struct{}),             // Unbuffered - used for signaling via close()
		outputFn: outputFn,
	}

	// Start processing events
	monitor.wg.Add(1)
	go monitor.processEvents()

	return monitor
}

// Events implements StateMonitor interface
func (sm *stateMonitor) Events() chan<- StateTransition {
	return sm.events
}

// Close implements io.Closer interface for graceful shutdown
func (sm *stateMonitor) Close() error {
	// Signal shutdown
	close(sm.done)

	// Wait for the processEvents goroutine to finish
	sm.wg.Wait()

	return nil
}

// processEvents processes state transition events
func (sm *stateMonitor) processEvents() {
	defer sm.wg.Done()

	for {
		select {
		case transition := <-sm.events:
			// Process the transition - no dropping, let it block/crash if buffer fills
			sm.outputFn(transition)
		case <-sm.done:
			// Shutdown requested - drain remaining events before exiting
			for {
				select {
				case transition := <-sm.events:
					sm.outputFn(transition)
				default:
					// No more events to drain
					return
				}
			}
		}
	}
}

// CreateMonitorCallback creates a transition callback for the given monitors and manager name
// Takes a slice of monitors to allow constructors to build and modify the list before calling
func CreateMonitorCallback(managerName string, monitors []StateMonitor) stateless.TransitionFunc {
	// Filter out nil monitors
	activeMonitors := make([]StateMonitor, 0, len(monitors))
	for _, monitor := range monitors {
		if monitor != nil {
			activeMonitors = append(activeMonitors, monitor)
		}
	}

	return stateless.TransitionFunc(func(ctx context.Context, transition stateless.Transition) {
		if len(activeMonitors) == 0 {
			return
		}

		stateTransition := StateTransition{
			Name:    managerName,
			From:    transition.Source.(string),
			To:      transition.Destination.(string),
			Trigger: transition.Trigger.(string),
		}

		// Publish to all active monitors (non-blocking)
		for _, monitor := range activeMonitors {
			select {
			case monitor.Events() <- stateTransition:
				// Successfully sent
			default:
				// Channel full, drop the event
			}
		}
	})
}

// CloseMonitors gracefully closes all monitors that implement io.Closer
func CloseMonitors(monitors []StateMonitor, timeout time.Duration) {
	for _, monitor := range monitors {
		if closer, ok := monitor.(io.Closer); ok {
			// For monitors that implement io.Closer, we call Close() directly
			// The timeout handling should be implemented by the monitor itself
			closer.Close()
		}
	}
}
