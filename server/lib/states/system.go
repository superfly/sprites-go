package states

import (
	"context"
	"fmt"
	"sync"

	"github.com/qmuntal/stateless"
)

// SystemStateManager coordinates the overall system state by listening to
// transitions from independent component state managers
type SystemStateManager struct {
	// State manager
	sm *stateless.StateMachine

	// Current state tracking
	mu           sync.RWMutex
	currentState string

	// Component state tracking (updated via OnTransitioned callbacks)
	componentStates map[string]string // componentID -> current state
	processState    string
	processExitCode int

	// Dependencies (injected)
	logger       interface{} // Will be set to concrete logger
	tlaTracer    interface{} // Will be set to concrete TLA tracer
	errorHandler interface{} // Will be set to concrete error handler
}

// NewSystemStateManager creates a new system state manager
func NewSystemStateManager() *SystemStateManager {
	return &SystemStateManager{
		currentState:    SystemInitializing,
		componentStates: make(map[string]string),
		processState:    ProcessInitializing,
		processExitCode: 0,
	}
}

// Initialize sets up the system state manager
func (ssm *SystemStateManager) Initialize() error {
	// Create state manager with simple state storage
	ssm.sm = stateless.NewStateMachine(SystemInitializing)

	// Configure state transitions based on component states
	ssm.configureStateTransitions()

	// Emit initial TLA trace
	ssm.updateTLATracer()

	return nil
}

// configureStateTransitions sets up the system state transitions
func (ssm *SystemStateManager) configureStateTransitions() {
	// Initializing -> Running (when all components and process are ready)
	ssm.sm.Configure(SystemInitializing).
		Permit(TriggerSystemStart, SystemRunning, ssm.canTransitionToRunning)

	// Running -> Error (when any component or process fails)
	ssm.sm.Configure(SystemRunning).
		Permit(TriggerSystemError, SystemError, ssm.shouldTransitionToError).
		Permit(TriggerShutdownStart, SystemShuttingDown)

	// Error state - execute business logic
	ssm.sm.Configure(SystemError).
		OnEntry(func(ctx context.Context, args ...any) error {
			return ssm.handleSystemError(ctx)
		})

	// ShuttingDown -> Shutdown (when all components are shut down)
	ssm.sm.Configure(SystemShuttingDown).
		Permit(TriggerShutdownComplete, SystemShutdown, ssm.canCompleteShutdown).
		OnEntry(func(ctx context.Context, args ...any) error {
			// Initiate shutdown of all components
			return ssm.initiateComponentShutdown(ctx)
		})

	// Final shutdown state
	ssm.sm.Configure(SystemShutdown).
		OnEntry(func(ctx context.Context, args ...any) error {
			// System fully shut down
			return nil
		})

	// Set up global transition listener for external communication
	ssm.sm.OnTransitioned(func(ctx context.Context, transition stateless.Transition) {
		ssm.onSystemStateTransitioned(ctx, transition)
	})
}

// Component state update methods - called by component state managers via OnTransitioned

// OnComponentTransition is called when any component state changes
func (ssm *SystemStateManager) OnComponentTransition(ctx context.Context, componentID string, transition stateless.Transition) error {
	ssm.mu.Lock()
	oldState := ssm.componentStates[componentID]
	newState := transition.Destination.(string)
	ssm.componentStates[componentID] = newState
	ssm.mu.Unlock()

	// Debug logging would go here
	// ssm.logger.Debug("Component state changed", "component", componentID, "from", oldState, "to", newState)
	_ = oldState

	// Update TLA tracer immediately when component state changes
	ssm.updateTLATracer()

	// Evaluate if system state should change
	return ssm.evaluateSystemTransitions(ctx)
}

// OnProcessTransition is called when process state changes
func (ssm *SystemStateManager) OnProcessTransition(ctx context.Context, transition stateless.Transition) error {
	ssm.mu.Lock()
	oldState := ssm.processState
	ssm.processState = transition.Destination.(string)

	// Extract exit code from transition data if available
	if exitCode, ok := transition.Source.(int); ok {
		ssm.processExitCode = exitCode
	}
	ssm.mu.Unlock()

	// Debug logging would go here
	// ssm.logger.Debug("Process state changed", "from", oldState, "to", ssm.processState)
	_ = oldState

	// Update TLA tracer immediately when process state changes
	ssm.updateTLATracer()

	// Evaluate if system state should change
	return ssm.evaluateSystemTransitions(ctx)
}

// evaluateSystemTransitions checks if system state should transition based on current component/process states
func (ssm *SystemStateManager) evaluateSystemTransitions(ctx context.Context) error {
	triggers, err := ssm.sm.PermittedTriggersCtx(ctx)
	if err != nil {
		return fmt.Errorf("failed to get permitted triggers: %w", err)
	}

	// Try each possible transition based on current states
	for _, trigger := range triggers {
		if canFire, err := ssm.sm.CanFireCtx(ctx, trigger); err == nil && canFire {
			return ssm.sm.FireCtx(ctx, trigger)
		}
	}

	return nil
}

// Guard functions for state transitions

// canTransitionToRunning checks if system can transition to running
func (ssm *SystemStateManager) canTransitionToRunning(ctx context.Context, args ...any) bool {
	ssm.mu.RLock()
	defer ssm.mu.RUnlock()

	// All components must be running and process must be running
	allComponentsRunning := true
	for _, state := range ssm.componentStates {
		if state != ComponentRunning {
			allComponentsRunning = false
			break
		}
	}

	return allComponentsRunning && ssm.processState == ProcessRunning
}

// shouldTransitionToError checks if system should transition to error state
func (ssm *SystemStateManager) shouldTransitionToError(ctx context.Context, args ...any) bool {
	ssm.mu.RLock()
	defer ssm.mu.RUnlock()

	// Error conditions: any component failed or process crashed/killed/errored
	for _, state := range ssm.componentStates {
		if state == ComponentError {
			return true
		}
	}

	return ssm.processState == ProcessCrashed ||
		ssm.processState == ProcessKilled ||
		ssm.processState == ProcessError ||
		(ssm.processState == ProcessExited && ssm.processExitCode != 0)
}

// canCompleteShutdown checks if shutdown can be completed
func (ssm *SystemStateManager) canCompleteShutdown(ctx context.Context, args ...any) bool {
	ssm.mu.RLock()
	defer ssm.mu.RUnlock()

	// All components must be shut down and process must be stopped
	allComponentsShutdown := true
	for _, state := range ssm.componentStates {
		if state != ComponentShutdown {
			allComponentsShutdown = false
			break
		}
	}

	processStoppedStates := []string{ProcessStopped, ProcessExited, ProcessCrashed, ProcessKilled}
	processIsStopped := false
	for _, state := range processStoppedStates {
		if ssm.processState == state {
			processIsStopped = true
			break
		}
	}

	return allComponentsShutdown && processIsStopped
}

// Business logic handlers

// handleSystemError executes strongly typed error handling business logic
func (ssm *SystemStateManager) handleSystemError(ctx context.Context) error {
	// This would use the injected error handler with strong typing
	// Business logic would be in handlers package

	ssm.mu.RLock()
	processState := ssm.processState
	exitCode := ssm.processExitCode
	ssm.mu.RUnlock()

	// Placeholder for error handling logic
	_ = processState
	_ = exitCode

	return nil
}

// initiateComponentShutdown commands all components to begin shutdown
func (ssm *SystemStateManager) initiateComponentShutdown(ctx context.Context) error {
	// This would signal all registered components to start shutting down
	// The components would then emit their transitions as they shut down

	// Placeholder for shutdown initiation logic
	return nil
}

// onSystemStateTransitioned handles system state transitions for external communication
func (ssm *SystemStateManager) onSystemStateTransitioned(ctx context.Context, transition stateless.Transition) {
	// Update current state
	ssm.mu.Lock()
	ssm.currentState = transition.Destination.(string)
	ssm.mu.Unlock()

	// Update TLA tracer with system state
	ssm.updateTLATracer()
}

// updateTLATracer emits complete TLA+ state to tracer
func (ssm *SystemStateManager) updateTLATracer() {
	ssm.mu.RLock()
	defer ssm.mu.RUnlock()

	if ssm.tlaTracer == nil {
		return
	}

	// Type assert to get the actual TLA tracer
	if tracer, ok := ssm.tlaTracer.(interface {
		UpdateSystemState(string)
		UpdateComponentSetState(string)
		UpdateDBState(string)
		UpdateFSState(string)
		UpdateProcessState(string)
	}); ok {
		// Update system state (was overallState)
		tracer.UpdateSystemState(ssm.currentState)

		// Update component set state (aggregate of all components)
		componentSetState := ssm.determineComponentSetState()
		tracer.UpdateComponentSetState(componentSetState)

		// Update individual component states
		if dbState, exists := ssm.componentStates["db"]; exists {
			tracer.UpdateDBState(dbState)
		}
		if fsState, exists := ssm.componentStates["fs"]; exists {
			tracer.UpdateFSState(fsState)
		}

		// Update process state
		tracer.UpdateProcessState(ssm.processState)
	}
}

// determineComponentSetState calculates the aggregate component set state
func (ssm *SystemStateManager) determineComponentSetState() string {
	if len(ssm.componentStates) == 0 {
		return ComponentSetInitializing
	}

	allRunning := true
	allShutdown := true
	allShuttingDown := true
	hasError := false
	anyShuttingDown := false
	anyShutdown := false

	for _, state := range ssm.componentStates {
		switch state {
		case ComponentError:
			hasError = true
			allRunning = false
			allShutdown = false
			allShuttingDown = false
		case ComponentRunning:
			// Component is running - not shutdown or shutting down
			allShutdown = false
			allShuttingDown = false
		case ComponentShutdown:
			// Component is shut down - not running or shutting down
			allRunning = false
			allShuttingDown = false
			anyShutdown = true
		case ComponentShuttingDown:
			// Component is shutting down - not running or shutdown
			allRunning = false
			allShutdown = false
			anyShuttingDown = true
		case ComponentStarting:
			// Component is starting - not running, not shutdown, not shutting down
			allRunning = false
			allShutdown = false
			allShuttingDown = false
		default:
			// Initializing or other states - not running, not shutdown, not shutting down
			allRunning = false
			allShutdown = false
			allShuttingDown = false
		}
	}

	if hasError {
		return ComponentSetError
	}
	if allShutdown {
		return ComponentSetShutdown
	}
	if allShuttingDown && !allRunning {
		return ComponentSetShuttingDown
	}
	if allRunning {
		return ComponentSetRunning
	}

	// Context-aware fallback logic
	// If we're in shutdown mode and have mixed states, prefer shutdown-related states
	if ssm.currentState == SystemShuttingDown || ssm.currentState == SystemShutdown {
		if anyShuttingDown || anyShutdown {
			// During shutdown, prefer ShuttingDown over Initializing
			return ComponentSetShuttingDown
		}
	}

	// If any component is starting or in transition states during startup, remain in initializing
	return ComponentSetInitializing
}

// Component registration for dynamic components

// RegisterComponent adds a new component to be tracked
func (ssm *SystemStateManager) RegisterComponent(componentID string, initialState string) {
	ssm.mu.Lock()
	defer ssm.mu.Unlock()
	ssm.componentStates[componentID] = initialState
}

// UnregisterComponent removes a component from tracking
func (ssm *SystemStateManager) UnregisterComponent(componentID string) {
	ssm.mu.Lock()
	defer ssm.mu.Unlock()
	delete(ssm.componentStates, componentID)
}

// Command interface for external control

// TriggerShutdown explicitly commands the system to start shutting down
func (ssm *SystemStateManager) TriggerShutdown(ctx context.Context) error {
	return ssm.sm.FireCtx(ctx, TriggerShutdownStart)
}

// GetCurrentState returns the current system state
func (ssm *SystemStateManager) GetCurrentState() string {
	ssm.mu.RLock()
	defer ssm.mu.RUnlock()
	return ssm.currentState
}

// GetComponentStates returns current states of all tracked components
func (ssm *SystemStateManager) GetComponentStates() map[string]string {
	ssm.mu.RLock()
	defer ssm.mu.RUnlock()

	// Return a copy to prevent external modification
	states := make(map[string]string)
	for k, v := range ssm.componentStates {
		states[k] = v
	}
	return states
}

// SetTLATracer sets the TLA tracer for state emissions
func (ssm *SystemStateManager) SetTLATracer(tracer interface{}) {
	ssm.mu.Lock()
	defer ssm.mu.Unlock()
	ssm.tlaTracer = tracer
}
