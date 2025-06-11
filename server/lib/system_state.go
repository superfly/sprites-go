package lib

import (
	"context"

	"github.com/qmuntal/stateless"
)

// SystemStateType represents the basic system states
type SystemStateType string

const (
	SystemStateInitializing  SystemStateType = "Initializing"
	SystemStateReady         SystemStateType = "Ready"
	SystemStateRunning       SystemStateType = "Running"
	SystemStateCheckpointing SystemStateType = "Checkpointing"
	SystemStateRestoring     SystemStateType = "Restoring"
	SystemStateShuttingDown  SystemStateType = "ShuttingDown"
	SystemStateShutdown      SystemStateType = "Shutdown"
	SystemStateError         SystemStateType = "Error"
)

// SystemTrigger represents the triggers that cause system state transitions
type SystemTrigger string

const (
	SystemTriggerStart               SystemTrigger = "Start"
	SystemTriggerReady               SystemTrigger = "Ready"
	SystemTriggerRun                 SystemTrigger = "Run"
	SystemTriggerShutdownRequested   SystemTrigger = "ShutdownRequested"
	SystemTriggerCheckpointRequested SystemTrigger = "CheckpointRequested"
	SystemTriggerRestoreRequested    SystemTrigger = "RestoreRequested"
	SystemTriggerCompleted           SystemTrigger = "Completed"
	SystemTriggerFailed              SystemTrigger = "Failed"
)

// ErrorType represents the types of errors
type ErrorType string

const (
	ErrorTypeNone            ErrorType = "None"
	ErrorTypeDBError         ErrorType = "DBError"
	ErrorTypeFSError         ErrorType = "FSError"
	ErrorTypeProcessError    ErrorType = "ProcessError"
	ErrorTypeProcessCrash    ErrorType = "ProcessCrash"
	ErrorTypeProcessKilled   ErrorType = "ProcessKilled"
	ErrorTypeCheckpointError ErrorType = "CheckpointError"
	ErrorTypeRestoreError    ErrorType = "RestoreError"
	ErrorTypeStartupError    ErrorType = "StartupError"
)

// SystemState manages the overall system state
type SystemState struct {
	*stateless.StateMachine
	componentSetState *ComponentSetState
	processState      *ProcessState
	errorType         ErrorType
}

// NewSystemState creates a new system state machine
func NewSystemState(componentSetSM *ComponentSetState, processSM *ProcessState) *SystemState {
	ssm := &SystemState{
		componentSetState: componentSetSM,
		processState:      processSM,
		errorType:         ErrorTypeNone,
	}

	// Create the state machine starting in the initializing state
	ssm.StateMachine = stateless.NewStateMachine(SystemStateInitializing)
	ssm.configureStateMachine()

	// Set up reactive coordination - listen to dependency state changes
	ssm.setupReactiveCoordination()

	// Activate the state machine to trigger OnEntry callbacks
	ssm.Activate()

	// Manually trigger initialization since OnEntry doesn't fire when starting in that state
	// This starts the component set
	ssm.componentSetState.Fire(ComponentSetTriggerStart)

	return ssm
}

// setupReactiveCoordination sets up listeners for automatic state coordination
func (ssm *SystemState) setupReactiveCoordination() {
	// Listen to component set state changes
	ssm.componentSetState.OnTransitioned(func(ctx context.Context, transition stateless.Transition) {
		ssm.handleDependencyStateChange()
	})

	// Listen to process state changes
	ssm.processState.OnTransitioned(func(ctx context.Context, transition stateless.Transition) {
		ssm.handleDependencyStateChange()
	})
}

// handleDependencyStateChange reacts to component set and process state changes
func (ssm *SystemState) handleDependencyStateChange() {
	currentSystemState := ssm.GetState()
	componentSetState := ssm.componentSetState.GetState()
	processState := ssm.processState.GetState()

	// Auto-transition Initializing -> Ready when component set is ready
	if currentSystemState == SystemStateInitializing &&
		componentSetState == ComponentSetStateRunning {
		go func() {
			ssm.Fire(SystemTriggerReady)
		}()
		return
	}

	// Auto-transition Ready -> Running when both dependencies are ready
	if currentSystemState == SystemStateReady &&
		componentSetState == ComponentSetStateRunning &&
		processState == ProcessStateRunning {
		ssm.Fire(SystemTriggerRun)
		return
	}

	// Auto-transition to error states when dependencies fail
	if componentSetState == ComponentSetStateError {
		ssm.SetErrorType(ErrorTypeDBError) // or determine specific error type
		ssm.Fire(SystemTriggerFailed)
		return
	}

	if processState == ProcessStateError || processState == ProcessStateCrashed || processState == ProcessStateKilled {
		if processState == ProcessStateError {
			ssm.SetErrorType(ErrorTypeProcessError)
		} else if processState == ProcessStateCrashed {
			ssm.SetErrorType(ErrorTypeProcessCrash)
		} else if processState == ProcessStateKilled {
			ssm.SetErrorType(ErrorTypeProcessKilled)
		}
		ssm.Fire(SystemTriggerFailed)
		return
	}

	// Auto-transition ShuttingDown -> Shutdown when both dependencies are shutdown
	if currentSystemState == SystemStateShuttingDown &&
		componentSetState == ComponentSetStateShutdown &&
		processState == ProcessStateStopped {
		ssm.Fire(SystemTriggerCompleted)
		return
	}

	// Auto-transition Checkpointing -> Running when checkpoint completes
	if currentSystemState == SystemStateCheckpointing &&
		componentSetState == ComponentSetStateRunning {
		ssm.Fire(SystemTriggerCompleted)
		return
	}

	// Auto-transition Restoring -> Running when restore completes
	if currentSystemState == SystemStateRestoring &&
		componentSetState == ComponentSetStateRunning {
		ssm.Fire(SystemTriggerCompleted)
		return
	}
}

// configureStateMachine sets up the state machine transitions
func (ssm *SystemState) configureStateMachine() {
	// Initializing state - can only start components, not go to Ready manually
	ssm.Configure(SystemStateInitializing).
		Permit(SystemTriggerReady, SystemStateReady). // Only fired by reactive logic
		Permit(SystemTriggerFailed, SystemStateError).
		OnEntry(func(ctx context.Context, args ...any) error {
			// Start component set when system initializes
			return ssm.componentSetState.Fire(ComponentSetTriggerStart)
		})

	// Ready state - process starts here when entering Ready
	ssm.Configure(SystemStateReady).
		Permit(SystemTriggerRun, SystemStateRunning). // Only fired automatically
		Permit(SystemTriggerShutdownRequested, SystemStateShuttingDown).
		Permit(SystemTriggerFailed, SystemStateError).
		OnEntry(func(ctx context.Context, args ...any) error {
			// Start process in separate goroutine = separate transaction
			go func() {
				ssm.processState.Fire(TriggerStart, context.Background())
			}()
			return nil // OnEntry completes immediately
		})

	// Running state
	ssm.Configure(SystemStateRunning).
		Permit(SystemTriggerShutdownRequested, SystemStateShuttingDown).
		Permit(SystemTriggerCheckpointRequested, SystemStateCheckpointing).
		Permit(SystemTriggerRestoreRequested, SystemStateRestoring).
		Permit(SystemTriggerFailed, SystemStateError)

	// Checkpointing state
	ssm.Configure(SystemStateCheckpointing).
		Permit(SystemTriggerCompleted, SystemStateRunning).
		Permit(SystemTriggerFailed, SystemStateError).
		OnEntry(func(ctx context.Context, args ...any) error {
			// Fire checkpoint on component set
			return ssm.componentSetState.Fire(ComponentSetTriggerCheckpoint)
		})

	// Restoring state
	ssm.Configure(SystemStateRestoring).
		Permit(SystemTriggerCompleted, SystemStateRunning).
		Permit(SystemTriggerFailed, SystemStateError).
		OnEntry(func(ctx context.Context, args ...any) error {
			// Fire restore on component set
			return ssm.componentSetState.Fire(ComponentSetTriggerRestore)
		})

	// Shutting down state
	ssm.Configure(SystemStateShuttingDown).
		Permit(SystemTriggerCompleted, SystemStateShutdown).
		Permit(SystemTriggerFailed, SystemStateError).
		OnEntry(func(ctx context.Context, args ...any) error {
			// Fire shutdown on both component set and process
			if err := ssm.componentSetState.Fire(ComponentSetTriggerShutdown); err != nil {
				return err
			}
			return ssm.processState.Fire(TriggerStop)
		})

	// Final states
	ssm.Configure(SystemStateShutdown)
	ssm.Configure(SystemStateError)
}

// GetState returns the current system state
func (ssm *SystemState) GetState() SystemStateType {
	return SystemStateType(ssm.MustState().(SystemStateType))
}

func (ssm *SystemState) GetProcessState() ProcessStateType {
	return ssm.processState.GetState()
}

func (ssm *SystemState) GetComponentSetState() ComponentSetStateType {
	return ssm.componentSetState.GetState()
}

// SetErrorType sets the current error type
func (ssm *SystemState) SetErrorType(errorType ErrorType) {
	ssm.errorType = errorType
}

// GetErrorType returns the current error type
func (ssm *SystemState) GetErrorType() ErrorType {
	return ssm.errorType
}

// AddStateChangeCallback adds a callback that will be called on any state change
func (ssm *SystemState) AddStateChangeCallback(callback func(stateless.Transition)) {
	ssm.OnTransitioned(func(ctx context.Context, transition stateless.Transition) {
		callback(transition)
	})
}
