package states

import (
	"context"
	"sync"

	"github.com/qmuntal/stateless"
)

// ComponentStateManager manages an individual component (DB, FS, etc.) state
type ComponentStateManager struct {
	// Component identity
	componentID   string
	componentType string // "DB", "FS", etc.

	// State manager
	sm *stateless.StateMachine

	// Current state tracking
	mu           sync.RWMutex
	currentState string

	// Communication callback (set by parent)
	onTransitionCallback func(ctx context.Context, componentID string, transition stateless.Transition) error

	// Dependencies (injected)
	logger       interface{} // Will be set to concrete logger
	errorHandler interface{} // Will be set to concrete error handler
}

// NewComponentStateManager creates a new component state manager
func NewComponentStateManager(componentID, componentType string) *ComponentStateManager {
	return &ComponentStateManager{
		componentID:   componentID,
		componentType: componentType,
		currentState:  ComponentInitializing,
	}
}

// Initialize sets up the component state manager
func (csm *ComponentStateManager) Initialize() error {
	// Create state manager with simple state storage
	csm.sm = stateless.NewStateMachine(ComponentInitializing)

	// Configure state transitions
	csm.configureStateTransitions()

	return nil
}

// SetTransitionCallback sets the callback for state transitions
func (csm *ComponentStateManager) SetTransitionCallback(callback func(ctx context.Context, componentID string, transition stateless.Transition) error) {
	csm.onTransitionCallback = callback
}

// configureStateTransitions sets up the component state transitions
func (csm *ComponentStateManager) configureStateTransitions() {
	// Initializing -> Starting
	csm.sm.Configure(ComponentInitializing).
		Permit(TriggerComponentStart, ComponentStarting)

	// Starting -> Running (when component is ready)
	csm.sm.Configure(ComponentStarting).
		Permit(TriggerComponentReady, ComponentRunning).
		Permit(TriggerComponentError, ComponentError).
		OnEntry(func(ctx context.Context, args ...any) error {
			// Business logic: start the component
			return csm.startComponent(ctx)
		})

	// Running -> Checkpointing/Restoring/Stopping/Error
	csm.sm.Configure(ComponentRunning).
		Permit(TriggerCheckpointBegin, ComponentCheckpointing).
		Permit(TriggerRestoreBegin, ComponentRestoring).
		Permit(TriggerComponentStop, ComponentStopping).
		Permit(TriggerComponentShutdown, ComponentShuttingDown).
		Permit(TriggerComponentError, ComponentError)

	// Checkpointing -> Running/Error
	csm.sm.Configure(ComponentCheckpointing).
		Permit(TriggerCheckpointFinish, ComponentRunning).
		Permit(TriggerComponentError, ComponentError).
		OnEntry(func(ctx context.Context, args ...any) error {
			// Business logic: perform checkpoint
			return csm.performCheckpoint(ctx)
		})

	// Restoring -> Running/Error
	csm.sm.Configure(ComponentRestoring).
		Permit(TriggerRestoreFinish, ComponentRunning).
		Permit(TriggerComponentError, ComponentError).
		OnEntry(func(ctx context.Context, args ...any) error {
			// Business logic: perform restore
			return csm.performRestore(ctx)
		})

	// Stopping -> Stopped
	csm.sm.Configure(ComponentStopping).
		Permit(TriggerComponentReady, ComponentStopped). // Use Ready as "Stop Complete"
		Permit(TriggerComponentError, ComponentError).
		OnEntry(func(ctx context.Context, args ...any) error {
			// Business logic: stop the component
			return csm.stopComponent(ctx)
		})

	// ShuttingDown -> Shutdown
	csm.sm.Configure(ComponentShuttingDown).
		Permit(TriggerComponentReady, ComponentShutdown). // Use Ready as "Shutdown Complete"
		Permit(TriggerComponentError, ComponentError).
		OnEntry(func(ctx context.Context, args ...any) error {
			// Business logic: shutdown the component
			return csm.shutdownComponent(ctx)
		})

	// Error state - handle errors
	csm.sm.Configure(ComponentError).
		OnEntry(func(ctx context.Context, args ...any) error {
			// Business logic: handle component error
			return csm.handleComponentError(ctx)
		})

	// Final states are terminal
	csm.sm.Configure(ComponentStopped)
	csm.sm.Configure(ComponentShutdown)

	// Set up transition callback to communicate with SystemStateManager
	csm.sm.OnTransitioned(func(ctx context.Context, transition stateless.Transition) {
		csm.onComponentTransitioned(ctx, transition)
	})
}

// onComponentTransitioned handles state transitions and notifies the system
func (csm *ComponentStateManager) onComponentTransitioned(ctx context.Context, transition stateless.Transition) {
	// Update current state
	csm.mu.Lock()
	csm.currentState = transition.Destination.(string)
	csm.mu.Unlock()

	// Notify SystemStateManager if callback is set
	if csm.onTransitionCallback != nil {
		if err := csm.onTransitionCallback(ctx, csm.componentID, transition); err != nil {
			// Log error but don't fail the transition
			// csm.logger.Error("Failed to notify system of transition", "error", err)
			_ = err
		}
	}
}

// Business logic methods - these would contain the actual component-specific logic

// startComponent contains component-specific startup logic
func (csm *ComponentStateManager) startComponent(ctx context.Context) error {
	// Component-specific startup logic would go here
	// For DB: connect to database, verify connection
	// For FS: mount filesystem, verify mount

	// For now, simulate async startup and auto-transition to Ready
	go func() {
		// Simulate component startup time
		// In real implementation, this would wait for actual component to be ready
		// then fire TriggerComponentReady

		// Auto-transition to ready for demo
		if err := csm.sm.FireCtx(ctx, TriggerComponentReady); err != nil {
			// Handle error
			csm.sm.FireCtx(ctx, TriggerComponentError)
		}
	}()

	return nil
}

// performCheckpoint contains component-specific checkpoint logic
func (csm *ComponentStateManager) performCheckpoint(ctx context.Context) error {
	// Component-specific checkpoint logic would go here
	// For DB: create database snapshot
	// For FS: create filesystem snapshot

	// Auto-transition to complete for demo
	go func() {
		// Simulate checkpoint work
		if err := csm.sm.FireCtx(ctx, TriggerCheckpointFinish); err != nil {
			csm.sm.FireCtx(ctx, TriggerComponentError)
		}
	}()

	return nil
}

// performRestore contains component-specific restore logic
func (csm *ComponentStateManager) performRestore(ctx context.Context) error {
	// Component-specific restore logic would go here
	// For DB: restore database from snapshot
	// For FS: restore filesystem from snapshot

	// Auto-transition to complete for demo
	go func() {
		// Simulate restore work
		if err := csm.sm.FireCtx(ctx, TriggerRestoreFinish); err != nil {
			csm.sm.FireCtx(ctx, TriggerComponentError)
		}
	}()

	return nil
}

// stopComponent contains component-specific stop logic
func (csm *ComponentStateManager) stopComponent(ctx context.Context) error {
	// Component-specific stop logic would go here
	// For DB: close database connections
	// For FS: unmount filesystem

	// Auto-transition to complete for demo
	go func() {
		// Simulate stop work
		if err := csm.sm.FireCtx(ctx, TriggerComponentReady); err != nil {
			csm.sm.FireCtx(ctx, TriggerComponentError)
		}
	}()

	return nil
}

// shutdownComponent contains component-specific shutdown logic
func (csm *ComponentStateManager) shutdownComponent(ctx context.Context) error {
	// Component-specific shutdown logic would go here
	// Similar to stop but more graceful/complete

	// Auto-transition to complete for demo
	go func() {
		// Simulate shutdown work
		if err := csm.sm.FireCtx(ctx, TriggerComponentReady); err != nil {
			csm.sm.FireCtx(ctx, TriggerComponentError)
		}
	}()

	return nil
}

// handleComponentError contains component-specific error handling
func (csm *ComponentStateManager) handleComponentError(ctx context.Context) error {
	// Component-specific error handling would go here
	// This would use the injected error handler with strong typing

	return nil
}

// Command interface for external control

// TriggerStart commands the component to start
func (csm *ComponentStateManager) TriggerStart(ctx context.Context) error {
	return csm.sm.FireCtx(ctx, TriggerComponentStart)
}

// TriggerStop commands the component to stop
func (csm *ComponentStateManager) TriggerStop(ctx context.Context) error {
	return csm.sm.FireCtx(ctx, TriggerComponentStop)
}

// TriggerShutdown commands the component to shutdown
func (csm *ComponentStateManager) TriggerShutdown(ctx context.Context) error {
	return csm.sm.FireCtx(ctx, TriggerComponentShutdown)
}

// TriggerCheckpoint commands the component to begin checkpointing
func (csm *ComponentStateManager) TriggerCheckpoint(ctx context.Context) error {
	return csm.sm.FireCtx(ctx, TriggerCheckpointBegin)
}

// TriggerRestore commands the component to begin restoring
func (csm *ComponentStateManager) TriggerRestore(ctx context.Context) error {
	return csm.sm.FireCtx(ctx, TriggerRestoreBegin)
}

// TriggerError commands the component to transition to error state
func (csm *ComponentStateManager) TriggerError(ctx context.Context) error {
	return csm.sm.FireCtx(ctx, TriggerComponentError)
}

// State query interface

// GetCurrentState returns the current component state
func (csm *ComponentStateManager) GetCurrentState() string {
	csm.mu.RLock()
	defer csm.mu.RUnlock()
	return csm.currentState
}

// GetComponentID returns the component's unique identifier
func (csm *ComponentStateManager) GetComponentID() string {
	return csm.componentID
}

// GetComponentType returns the component's type (DB, FS, etc.)
func (csm *ComponentStateManager) GetComponentType() string {
	return csm.componentType
}
