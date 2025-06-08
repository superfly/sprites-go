package states

import "github.com/qmuntal/stateless"

// System States (from TLA+ spec SystemStates) - replaces "Overall"
const (
	SystemInitializing  = "Initializing"
	SystemRunning       = "Running"
	SystemCheckpointing = "Checkpointing"
	SystemRestoring     = "Restoring"
	SystemError         = "Error"
	SystemShuttingDown  = "ShuttingDown"
	SystemShutdown      = "Shutdown"
)

// Component States (from TLA+ spec ComponentStates)
const (
	ComponentInitializing  = "Initializing"
	ComponentStarting      = "Starting"
	ComponentRunning       = "Running"
	ComponentCheckpointing = "Checkpointing" // Added for TLA+ spec compliance
	ComponentRestoring     = "Restoring"     // Added for TLA+ spec compliance
	ComponentStopping      = "Stopping"
	ComponentShuttingDown  = "ShuttingDown"
	ComponentStopped       = "Stopped"
	ComponentShutdown      = "Shutdown"
	ComponentError         = "Error"
)

// Component Set States (aggregate of individual components)
const (
	ComponentSetInitializing  = "Initializing"
	ComponentSetRunning       = "Running"
	ComponentSetCheckpointing = "Checkpointing"
	ComponentSetRestoring     = "Restoring"
	ComponentSetShuttingDown  = "ShuttingDown"
	ComponentSetShutdown      = "Shutdown"
	ComponentSetError         = "Error"
)

// Process States (from TLA+ spec ProcessStates)
const (
	ProcessInitializing = "Initializing"
	ProcessStarting     = "Starting"
	ProcessRunning      = "Running"
	ProcessStopping     = "Stopping"
	ProcessSignaling    = "Signaling"
	ProcessStopped      = "Stopped"
	ProcessExited       = "Exited"
	ProcessCrashed      = "Crashed"
	ProcessKilled       = "Killed"
	ProcessError        = "Error"
)

// Reactive Event Types - for implementing the cascade pattern
const (
	EventProcessExited      = "ProcessExited"
	EventProcessCrashed     = "ProcessCrashed"
	EventProcessKilled      = "ProcessKilled"
	EventSystemStateChanged = "SystemStateChanged"
	EventComponentSetError  = "ComponentSetError"
	EventShutdownRequired   = "ShutdownRequired"
)

// Triggers for System State Machine (replaces Overall)
const (
	TriggerSystemStart          = "SystemStart"
	TriggerComponentsReady      = "ComponentsReady"
	TriggerSystemProcessStarted = "SystemProcessStarted"
	TriggerCheckpointStart      = "CheckpointStart"
	TriggerCheckpointComplete   = "CheckpointComplete"
	TriggerRestoreStart         = "RestoreStart"
	TriggerRestoreComplete      = "RestoreComplete"
	TriggerSystemError          = "SystemError"
	TriggerShutdownStart        = "ShutdownStart"
	TriggerShutdownComplete     = "ShutdownComplete"
	TriggerSystemProcessExited  = "SystemProcessExited"  // NEW: React to process exit
	TriggerSystemProcessCrashed = "SystemProcessCrashed" // NEW: React to process crash
	TriggerSystemProcessKilled  = "SystemProcessKilled"  // NEW: React to process kill
)

// Triggers for Component State Machines
const (
	TriggerComponentStart    = "Start"
	TriggerComponentReady    = "Ready"
	TriggerComponentStop     = "Stop"
	TriggerComponentShutdown = "Shutdown"
	TriggerComponentError    = "Error"
	TriggerCheckpointBegin   = "CheckpointBegin"
	TriggerCheckpointFinish  = "CheckpointFinish"
	TriggerRestoreBegin      = "RestoreBegin"
	TriggerRestoreFinish     = "RestoreFinish"
)

// Triggers for Component Set State Machine
const (
	TriggerComponentSetError    = "Error"
	TriggerComponentSetShutdown = "Shutdown"
	TriggerSystemToError        = "SystemToError"        // NEW: React to system error
	TriggerSystemToShuttingDown = "SystemToShuttingDown" // NEW: React to system shutdown
)

// Triggers for Process State Machine
const (
	TriggerProcessStart   = "Start"
	TriggerProcessStarted = "Started"
	TriggerProcessStop    = "Stop"
	TriggerProcessExited  = "Exited"
	TriggerProcessCrashed = "Crashed"
	TriggerProcessKilled  = "Killed"
	TriggerProcessError   = "Error"
	TriggerProcessSignal  = "Signal"
)

// Signal Types (from TLA+ spec Signals)
const (
	SignalNone    = "None"
	SignalSIGTERM = "SIGTERM"
	SignalSIGINT  = "SIGINT"
	SignalSIGKILL = "SIGKILL"
)

// ReactiveEvent represents an event that triggers reactive state changes
type ReactiveEvent struct {
	Type     string
	Source   string      // Which state machine triggered this
	Data     interface{} // Additional event data
	ExitCode *int        // For process exit events
}

// Helper functions for state machine configuration

// IsTransitionState checks if a state is a transition state (from TLA+ spec)
func IsTransitionState(state stateless.State) bool {
	transitionStates := []string{
		SystemInitializing, SystemShuttingDown,
		ComponentInitializing, ComponentStarting, ComponentStopping, ComponentShuttingDown,
		ProcessInitializing, ProcessStarting, ProcessStopping, ProcessSignaling,
	}

	stateStr := state.(string)
	for _, ts := range transitionStates {
		if stateStr == ts {
			return true
		}
	}
	return false
}

// IsFinalState checks if a state is a final state (from TLA+ spec)
func IsFinalState(state stateless.State) bool {
	finalStates := []string{
		SystemShutdown,
		ComponentStopped, ComponentShutdown,
		ProcessStopped, ProcessExited, ProcessCrashed, ProcessKilled,
	}

	stateStr := state.(string)
	for _, fs := range finalStates {
		if stateStr == fs {
			return true
		}
	}
	return false
}

// IsActiveState checks if a state is an active state (from TLA+ spec)
func IsActiveState(state stateless.State) bool {
	activeStates := []string{
		SystemRunning, SystemCheckpointing, SystemRestoring,
		ComponentRunning,
		ProcessRunning,
	}

	stateStr := state.(string)
	for _, as := range activeStates {
		if stateStr == as {
			return true
		}
	}
	return false
}

// IsErrorState checks if a state is an error state (from TLA+ spec)
func IsErrorState(state stateless.State) bool {
	errorStates := []string{
		SystemError,
		ComponentError,
		ProcessError,
	}

	stateStr := state.(string)
	for _, es := range errorStates {
		if stateStr == es {
			return true
		}
	}
	return false
}
