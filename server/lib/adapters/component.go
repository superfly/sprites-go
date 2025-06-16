package adapters

import (
	"context"
	"sync"
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

// BaseComponent provides common event handling and context management for components.
type BaseComponent struct {
	ctx     context.Context
	cancel  context.CancelFunc
	eventCh chan ComponentEventType // Buffered - external resource with unpredictable timing, consumers need reliable delivery
	eventWg sync.WaitGroup          // Tracks event emission goroutines
}

// NewBaseComponent creates a new BaseComponent with the given context.
func NewBaseComponent(ctx context.Context) *BaseComponent {
	childCtx, cancel := context.WithCancel(ctx)
	return &BaseComponent{
		ctx:     childCtx,
		cancel:  cancel,
		eventCh: make(chan ComponentEventType, 10), // Buffered channel with some buffer
	}
}

// Events returns the unbuffered channel for listening to component events
func (b *BaseComponent) Events() <-chan ComponentEventType {
	return b.eventCh
}

// EmitEvent sends an event to the channel using non-blocking goroutine pattern
func (b *BaseComponent) EmitEvent(event ComponentEventType) {
	// Run emission in a goroutine to avoid blocking the component
	// Use context to ensure proper cleanup and WaitGroup to track completion
	b.eventWg.Add(1)
	go func() {
		defer b.eventWg.Done()
		// Check if context is canceled before emitting event
		select {
		case <-b.ctx.Done():
			return // Context canceled, don't emit event
		case b.eventCh <- event:
			// Event sent successfully - no default case, let it block/crash if buffer fills
		}
	}()
}

// EmitEventSync sends an event synchronously to maintain order
func (b *BaseComponent) EmitEventSync(event ComponentEventType) {
	// Send synchronously when event order matters
	select {
	case <-b.ctx.Done():
		return // Context canceled, don't emit event
	case b.eventCh <- event:
		// Event sent successfully
	}
}

// Close permanently disposes of the base component resources
func (b *BaseComponent) Close() error {
	// Cancel context to stop event goroutines
	if b.cancel != nil {
		b.cancel()
	}

	// Wait for all event emission goroutines to complete before closing the channel
	// This ensures all events are processed before the component goes away
	b.eventWg.Wait()

	// Close the event channel to signal no more events will be sent
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
