package managers

import (
	"context"

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
