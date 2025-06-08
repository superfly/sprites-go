package states

import (
	"context"
	"fmt"
	"os"
	"sync"
	"syscall"

	"github.com/qmuntal/stateless"
)

// ProcessStateManager manages the supervised process state
type ProcessStateManager struct {
	// State manager
	sm *stateless.StateMachine

	// Current state tracking
	mu           sync.RWMutex
	currentState string

	// Process information
	process  *os.Process
	exitCode int
	signal   string

	// Communication callback (set by parent)
	onTransitionCallback func(ctx context.Context, transition stateless.Transition) error

	// Dependencies (injected)
	logger       interface{} // Will be set to concrete logger
	errorHandler interface{} // Will be set to concrete error handler
}

// NewProcessStateManager creates a new process state manager
func NewProcessStateManager() *ProcessStateManager {
	return &ProcessStateManager{
		currentState: ProcessInitializing,
		exitCode:     0,
		signal:       SignalNone,
	}
}

// Initialize sets up the process state manager
func (psm *ProcessStateManager) Initialize() error {
	// Create state manager with simple state storage
	psm.sm = stateless.NewStateMachine(ProcessInitializing)

	// Configure state transitions
	psm.configureStateTransitions()

	return nil
}

// SetTransitionCallback sets the callback for state transitions
func (psm *ProcessStateManager) SetTransitionCallback(callback func(ctx context.Context, transition stateless.Transition) error) {
	psm.onTransitionCallback = callback
}

// configureStateTransitions sets up the process state transitions
func (psm *ProcessStateManager) configureStateTransitions() {
	// Initializing -> Starting
	psm.sm.Configure(ProcessInitializing).
		Permit(TriggerProcessStart, ProcessStarting)

	// Starting -> Running/Error
	psm.sm.Configure(ProcessStarting).
		Permit(TriggerProcessStarted, ProcessRunning).
		Permit(TriggerProcessError, ProcessError).
		OnEntry(func(ctx context.Context, args ...any) error {
			// Business logic: start the process
			return psm.startProcess(ctx)
		})

	// Running -> Stopping/Signaling/Crashed/Killed/Exited/Error
	psm.sm.Configure(ProcessRunning).
		Permit(TriggerProcessStop, ProcessStopping).
		Permit(TriggerProcessSignal, ProcessSignaling).
		Permit(TriggerProcessCrashed, ProcessCrashed).
		Permit(TriggerProcessKilled, ProcessKilled).
		Permit(TriggerProcessExited, ProcessExited).
		Permit(TriggerProcessError, ProcessError)

	// Stopping -> Stopped/Error
	psm.sm.Configure(ProcessStopping).
		Permit(TriggerProcessStarted, ProcessStopped). // Use Started as "Stop Complete"
		Permit(TriggerProcessError, ProcessError).
		OnEntry(func(ctx context.Context, args ...any) error {
			// Business logic: gracefully stop the process
			return psm.stopProcess(ctx)
		})

	// Signaling -> Running/Stopped/Error (depending on signal effect)
	psm.sm.Configure(ProcessSignaling).
		Permit(TriggerProcessStarted, ProcessRunning). // Signal handled, continue running
		Permit(TriggerProcessExited, ProcessStopped).  // Signal caused graceful exit
		Permit(TriggerProcessCrashed, ProcessCrashed). // Signal caused crash
		Permit(TriggerProcessKilled, ProcessKilled).   // Signal caused kill
		Permit(TriggerProcessError, ProcessError).
		OnEntry(func(ctx context.Context, args ...any) error {
			// Business logic: send signal to process
			return psm.signalProcess(ctx)
		})

	// Error state - handle errors
	psm.sm.Configure(ProcessError).
		OnEntry(func(ctx context.Context, args ...any) error {
			// Business logic: handle process error
			return psm.handleProcessError(ctx)
		})

	// Final states are terminal
	psm.sm.Configure(ProcessStopped)
	psm.sm.Configure(ProcessExited)
	psm.sm.Configure(ProcessCrashed)
	psm.sm.Configure(ProcessKilled)

	// Set up transition callback to communicate with SystemStateManager
	psm.sm.OnTransitioned(func(ctx context.Context, transition stateless.Transition) {
		psm.onProcessTransitioned(ctx, transition)
	})
}

// onProcessTransitioned handles state transitions and notifies the system
func (psm *ProcessStateManager) onProcessTransitioned(ctx context.Context, transition stateless.Transition) {
	// Update current state
	psm.mu.Lock()
	psm.currentState = transition.Destination.(string)
	psm.mu.Unlock()

	// Notify SystemStateManager if callback is set
	if psm.onTransitionCallback != nil {
		if err := psm.onTransitionCallback(ctx, transition); err != nil {
			// Log error but don't fail the transition
			// psm.logger.Error("Failed to notify system of transition", "error", err)
			_ = err
		}
	}
}

// Business logic methods - these would contain the actual process management logic

// startProcess contains process startup logic
func (psm *ProcessStateManager) startProcess(ctx context.Context) error {
	// Process startup logic would go here
	// This would start the actual supervised process

	// For now, simulate async startup and auto-transition to Started
	go func() {
		// Simulate process startup time
		// In real implementation, this would:
		// 1. Execute the process command
		// 2. Store the process reference
		// 3. Start monitoring the process
		// 4. Fire TriggerProcessStarted when ready

		// Auto-transition to started for demo
		if err := psm.sm.FireCtx(ctx, TriggerProcessStarted); err != nil {
			// Handle error
			psm.sm.FireCtx(ctx, TriggerProcessError)
		}
	}()

	return nil
}

// stopProcess contains graceful process stop logic
func (psm *ProcessStateManager) stopProcess(ctx context.Context) error {
	// Graceful process stop logic would go here
	// This would send SIGTERM and wait for graceful shutdown

	// Auto-transition to complete for demo
	go func() {
		// Simulate stop work
		if err := psm.sm.FireCtx(ctx, TriggerProcessStarted); err != nil {
			psm.sm.FireCtx(ctx, TriggerProcessError)
		}
	}()

	return nil
}

// signalProcess contains signal sending logic
func (psm *ProcessStateManager) signalProcess(ctx context.Context) error {
	// Signal sending logic would go here
	// This would send the specified signal to the process

	psm.mu.RLock()
	signal := psm.signal
	psm.mu.RUnlock()

	// Simulate signal handling
	go func() {
		switch signal {
		case SignalSIGTERM, SignalSIGINT:
			// Graceful signals - process should exit cleanly
			psm.sm.FireCtx(ctx, TriggerProcessExited)
		case SignalSIGKILL:
			// Force kill
			psm.sm.FireCtx(ctx, TriggerProcessKilled)
		default:
			// Other signals might not affect running state
			psm.sm.FireCtx(ctx, TriggerProcessStarted)
		}
	}()

	return nil
}

// handleProcessError contains process-specific error handling
func (psm *ProcessStateManager) handleProcessError(ctx context.Context) error {
	// Process-specific error handling would go here
	// This would use the injected error handler with strong typing

	return nil
}

// Process monitoring methods - these would be called by external process monitors

// OnProcessExit is called when the process exits
func (psm *ProcessStateManager) OnProcessExit(ctx context.Context, exitCode int) error {
	psm.mu.Lock()
	psm.exitCode = exitCode
	psm.mu.Unlock()

	if exitCode == 0 {
		return psm.sm.FireCtx(ctx, TriggerProcessExited)
	} else {
		return psm.sm.FireCtx(ctx, TriggerProcessCrashed)
	}
}

// OnProcessKilled is called when the process is killed by a signal
func (psm *ProcessStateManager) OnProcessKilled(ctx context.Context, signal syscall.Signal) error {
	psm.mu.Lock()
	psm.signal = fmt.Sprintf("SIG%s", signal.String())
	psm.mu.Unlock()

	return psm.sm.FireCtx(ctx, TriggerProcessKilled)
}

// OnProcessCrashed is called when the process crashes unexpectedly
func (psm *ProcessStateManager) OnProcessCrashed(ctx context.Context, reason string) error {
	// Store crash reason for error handling
	return psm.sm.FireCtx(ctx, TriggerProcessCrashed)
}

// Command interface for external control

// TriggerStart commands the process to start
func (psm *ProcessStateManager) TriggerStart(ctx context.Context) error {
	return psm.sm.FireCtx(ctx, TriggerProcessStart)
}

// TriggerStop commands the process to stop gracefully
func (psm *ProcessStateManager) TriggerStop(ctx context.Context) error {
	return psm.sm.FireCtx(ctx, TriggerProcessStop)
}

// TriggerSignal commands the process to receive a signal
func (psm *ProcessStateManager) TriggerSignal(ctx context.Context, signal string) error {
	psm.mu.Lock()
	psm.signal = signal
	psm.mu.Unlock()

	return psm.sm.FireCtx(ctx, TriggerProcessSignal)
}

// TriggerError commands the process to transition to error state
func (psm *ProcessStateManager) TriggerError(ctx context.Context) error {
	return psm.sm.FireCtx(ctx, TriggerProcessError)
}

// State query interface

// GetCurrentState returns the current process state
func (psm *ProcessStateManager) GetCurrentState() string {
	psm.mu.RLock()
	defer psm.mu.RUnlock()
	return psm.currentState
}

// GetExitCode returns the process exit code (if exited)
func (psm *ProcessStateManager) GetExitCode() int {
	psm.mu.RLock()
	defer psm.mu.RUnlock()
	return psm.exitCode
}

// GetSignal returns the last signal sent to the process
func (psm *ProcessStateManager) GetSignal() string {
	psm.mu.RLock()
	defer psm.mu.RUnlock()
	return psm.signal
}

// GetProcess returns the managed process (if running)
func (psm *ProcessStateManager) GetProcess() *os.Process {
	psm.mu.RLock()
	defer psm.mu.RUnlock()
	return psm.process
}

// SetProcess sets the managed process reference
func (psm *ProcessStateManager) SetProcess(process *os.Process) {
	psm.mu.Lock()
	defer psm.mu.Unlock()
	psm.process = process
}
