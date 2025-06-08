package handlers

import (
	"context"
	"fmt"
)

// SystemErrorType represents different types of system errors
type SystemErrorType string

const (
	ProcessCrashError SystemErrorType = "ProcessCrash"
	ProcessKillError  SystemErrorType = "ProcessKill"
	ComponentError    SystemErrorType = "ComponentError"
	StartupError      SystemErrorType = "StartupError"
)

// SystemErrorContext contains context about the error
type SystemErrorContext struct {
	ErrorType   SystemErrorType
	ProcessCode int
	Component   string
	Details     string
}

// SystemActions interface defines actions the system can take
type SystemActions interface {
	RestartProcess(ctx context.Context) error
	RestartComponent(ctx context.Context, component string) error
	InitiateShutdown(ctx context.Context) error
	AlertOperator(ctx context.Context, message string) error
}

// SystemErrorHandler handles system error states with strongly typed logic
type SystemErrorHandler struct {
	actions SystemActions
}

// NewSystemErrorHandler creates a new system error handler
func NewSystemErrorHandler(actions SystemActions) *SystemErrorHandler {
	return &SystemErrorHandler{
		actions: actions,
	}
}

// HandleError executes the appropriate error handling logic based on error type
func (h *SystemErrorHandler) HandleError(ctx context.Context, errorCtx SystemErrorContext) error {
	switch errorCtx.ErrorType {
	case ProcessCrashError:
		return h.handleProcessCrash(ctx, errorCtx)
	case ProcessKillError:
		return h.handleProcessKill(ctx, errorCtx)
	case ComponentError:
		return h.handleComponentError(ctx, errorCtx)
	case StartupError:
		return h.handleStartupError(ctx, errorCtx)
	default:
		return fmt.Errorf("unknown error type: %s", errorCtx.ErrorType)
	}
}

// handleProcessCrash handles when the supervised process crashes
func (h *SystemErrorHandler) handleProcessCrash(ctx context.Context, errorCtx SystemErrorContext) error {
	// Alert operator about the crash
	alertMsg := fmt.Sprintf("Process crashed with exit code %d", errorCtx.ProcessCode)
	if err := h.actions.AlertOperator(ctx, alertMsg); err != nil {
		return fmt.Errorf("failed to alert operator: %w", err)
	}

	// Decide whether to restart or shutdown based on exit code
	if errorCtx.ProcessCode == 1 || errorCtx.ProcessCode == 2 {
		// Recoverable errors - attempt restart
		return h.actions.RestartProcess(ctx)
	} else {
		// Non-recoverable errors - initiate shutdown
		return h.actions.InitiateShutdown(ctx)
	}
}

// handleProcessKill handles when the supervised process is killed
func (h *SystemErrorHandler) handleProcessKill(ctx context.Context, errorCtx SystemErrorContext) error {
	// Process was forcefully killed - this is usually intentional
	alertMsg := fmt.Sprintf("Process was killed (exit code %d)", errorCtx.ProcessCode)
	if err := h.actions.AlertOperator(ctx, alertMsg); err != nil {
		return fmt.Errorf("failed to alert operator: %w", err)
	}

	// For kills, we usually want to shutdown gracefully
	return h.actions.InitiateShutdown(ctx)
}

// handleComponentError handles when a storage component fails
func (h *SystemErrorHandler) handleComponentError(ctx context.Context, errorCtx SystemErrorContext) error {
	alertMsg := fmt.Sprintf("Component %s failed: %s", errorCtx.Component, errorCtx.Details)
	if err := h.actions.AlertOperator(ctx, alertMsg); err != nil {
		return fmt.Errorf("failed to alert operator: %w", err)
	}

	// Try to restart the specific component
	if err := h.actions.RestartComponent(ctx, errorCtx.Component); err != nil {
		// If component restart fails, shutdown the system
		return h.actions.InitiateShutdown(ctx)
	}

	return nil
}

// handleStartupError handles when the system fails during startup
func (h *SystemErrorHandler) handleStartupError(ctx context.Context, errorCtx SystemErrorContext) error {
	alertMsg := fmt.Sprintf("System startup failed: %s", errorCtx.Details)
	if err := h.actions.AlertOperator(ctx, alertMsg); err != nil {
		return fmt.Errorf("failed to alert operator: %w", err)
	}

	// Startup errors usually require shutdown
	return h.actions.InitiateShutdown(ctx)
}
