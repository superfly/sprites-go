package adapters

import (
	"context"
	"sync"
)

// ComponentEventType defines events that can be emitted by a component
type ComponentEventType string

const (
	// ComponentStarting is emitted when the component is about to be started.
	ComponentStarting ComponentEventType = "starting"
	// ComponentStarted is emitted when the start process has successfully started.
	ComponentStarted ComponentEventType = "started"
	// ComponentStopping is emitted when a stop sequence has been initiated.
	ComponentStopping ComponentEventType = "stopping"
	// ComponentStopped is emitted when the component has stopped.
	ComponentStopped ComponentEventType = "stopped"
	// ComponentChecking is emitted when the component is checking readiness.
	ComponentChecking ComponentEventType = "checking"
	// ComponentReady is emitted when the component is ready to handle traffic.
	ComponentReady ComponentEventType = "ready"
	// ComponentFailed is emitted when the component has failed permanently.
	ComponentFailed ComponentEventType = "failed"
	// ComponentCheckpointed is emitted when a checkpoint operation has been performed.
	ComponentCheckpointed ComponentEventType = "checkpointed"
	// ComponentRestored is emitted when a restore operation has been performed.
	ComponentRestored ComponentEventType = "restored"
)

// BaseComponent provides common event handling and context management for components.
type BaseComponent struct {
	events chan ComponentEventType
	mu     sync.Mutex
	ctx    context.Context
}

// NewBaseComponent creates a new BaseComponent
func NewBaseComponent(ctx context.Context) *BaseComponent {
	return &BaseComponent{
		events: make(chan ComponentEventType, 10), // Buffer for events
		ctx:    ctx,
	}
}

// Events returns the event channel for consumers to listen on
func (bc *BaseComponent) Events() <-chan ComponentEventType {
	return bc.events
}

// EmitEvent sends a component event to listeners
func (bc *BaseComponent) EmitEvent(event ComponentEventType) {
	bc.mu.Lock()
	defer bc.mu.Unlock()

	select {
	case bc.events <- event:
		// Event sent successfully
	case <-bc.ctx.Done():
		// Context cancelled, don't send event
	default:
		// Channel full or closed, drop event
		// This is acceptable for component events
	}
}

// EmitEventSync sends a component event to listeners synchronously
func (bc *BaseComponent) EmitEventSync(event ComponentEventType) {
	bc.mu.Lock()
	defer bc.mu.Unlock()

	select {
	case bc.events <- event:
		// Event sent successfully
	case <-bc.ctx.Done():
		// Context cancelled, don't send event
	}
}

// Close closes the event channel
func (bc *BaseComponent) Close() error {
	bc.mu.Lock()
	defer bc.mu.Unlock()

	if bc.events != nil {
		close(bc.events)
		bc.events = nil
	}
	return nil
}

// Component defines the interface that all components must implement
type Component interface {
	// GetName returns the component name
	GetName() string

	// Start begins the component startup process
	Start(ctx context.Context) error

	// Stop initiates component shutdown
	Stop()

	// Checkpoint performs a checkpoint operation with the given ID
	Checkpoint(checkpointID string) error

	// Restore performs a restore operation from the given checkpoint ID
	Restore(checkpointID string) error

	// Events returns a channel that emits component lifecycle events
	Events() <-chan ComponentEventType

	// Close permanently disposes of the component
	Close() error
}
