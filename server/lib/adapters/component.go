package adapters

import (
	"context"
)

// ComponentEventType defines the type of event that can be emitted by a component.
type ComponentEventType string

const (
	// ComponentStarting is emitted when the component is about to be started.
	ComponentStarting ComponentEventType = "starting"
	// ComponentStarted is emitted when the start process has successfully started.
	ComponentStarted ComponentEventType = "started"
	// ComponentChecking is emitted when the ready check is being performed.
	ComponentChecking ComponentEventType = "checking"
	// ComponentReady is emitted when the component is ready (ready script succeeded or no ready script).
	ComponentReady ComponentEventType = "ready"
	// ComponentStopping is emitted when a stop sequence has been initiated.
	ComponentStopping ComponentEventType = "stopping"
	// ComponentStopped is emitted when the component has stopped.
	ComponentStopped ComponentEventType = "stopped"
	// ComponentFailed is emitted when the component has failed permanently.
	ComponentFailed ComponentEventType = "failed"
)

// Typed Event Handler approach
// Each event type has its own handler function signature
type (
	Starting func()
	Started  func()
	Checking func()
	Ready    func()
	Stopping func()
	Stopped  func()
	Failed   func(error)
)

// ComponentEventHandlers allows registering specific typed handlers
type ComponentEventHandlers struct {
	Starting Starting
	Started  Started
	Checking Checking
	Ready    Ready
	Stopping Stopping
	Stopped  Stopped
	Failed   Failed
}

// ComponentConfig defines the interface for component configuration
// Implementations provide both configuration data and event handlers
type ComponentConfig interface {
	// GetEventHandlers returns the event handlers (can be empty)
	GetEventHandlers() ComponentEventHandlers
}

// BaseComponent provides shared event management functionality
// Embed this in concrete component implementations
type BaseComponent struct {
	handlers ComponentEventHandlers
}

// NewBaseComponent creates a new base component with event management
func NewBaseComponent(handlers ComponentEventHandlers) *BaseComponent {
	return &BaseComponent{
		handlers: handlers,
	}
}

// SetEventHandlers sets up Observer pattern callbacks for component events
func (b *BaseComponent) SetEventHandlers(handlers ComponentEventHandlers) {
	b.handlers = handlers
}

// EmitEvent calls the corresponding handler if set
func (b *BaseComponent) EmitEvent(event ComponentEventType, err ...error) {
	// Call handler if set (type-safe approach)
	switch event {
	case ComponentStarting:
		if b.handlers.Starting != nil {
			b.handlers.Starting()
		}
	case ComponentStarted:
		if b.handlers.Started != nil {
			b.handlers.Started()
		}
	case ComponentChecking:
		if b.handlers.Checking != nil {
			b.handlers.Checking()
		}
	case ComponentReady:
		if b.handlers.Ready != nil {
			b.handlers.Ready()
		}
	case ComponentStopping:
		if b.handlers.Stopping != nil {
			b.handlers.Stopping()
		}
	case ComponentStopped:
		if b.handlers.Stopped != nil {
			b.handlers.Stopped()
		}
	case ComponentFailed:
		if b.handlers.Failed != nil {
			var failErr error
			if len(err) > 0 {
				failErr = err[0]
			}
			b.handlers.Failed(failErr)
		}
	}
}

// Component defines the interface for component lifecycle management
type Component interface {
	// Start initiates the component startup process
	Start(ctx context.Context) error

	// Stop stops the component
	Stop()

	// Checkpoint performs a checkpoint operation on the component
	Checkpoint(ctx context.Context) error

	// Restore performs a restore operation on the component
	Restore(ctx context.Context) error

	// SetEventHandlers sets up Observer pattern callbacks
	SetEventHandlers(handlers ComponentEventHandlers)
}
