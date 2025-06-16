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

// BaseComponent provides shared event management functionality
// Embed this in concrete component implementations
type BaseComponent struct {
	eventCh chan ComponentEventType
}

// NewBaseComponent creates a new base component with event management
func NewBaseComponent() *BaseComponent {
	return &BaseComponent{
		eventCh: make(chan ComponentEventType), // Unbuffered channel as required
	}
}

// Events returns the unbuffered channel for listening to component events
func (b *BaseComponent) Events() <-chan ComponentEventType {
	return b.eventCh
}

// EmitEvent sends an event to the channel
func (b *BaseComponent) EmitEvent(event ComponentEventType) {
	// Direct blocking send with unbuffered channel
	b.eventCh <- event
}

// Close permanently disposes of the base component resources
func (b *BaseComponent) Close() error {
	if b.eventCh != nil {
		close(b.eventCh)
		b.eventCh = nil
	}
	return nil
}

// Component defines the interface for component lifecycle management
type Component interface {
	// GetName returns the component name for identification
	GetName() string

	// Start initiates the component startup process
	Start(ctx context.Context) error

	// Stop stops the component
	Stop()

	// Close permanently disposes of the component and all its resources
	Close() error

	// Checkpoint performs a checkpoint operation on the component
	Checkpoint() error

	// Restore performs a restore operation on the component
	Restore() error

	// Events returns a channel for listening to component events
	Events() <-chan ComponentEventType
}
