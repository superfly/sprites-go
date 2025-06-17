package managers

import (
	"context"
	"fmt"
	"os"

	"sprite-env/lib"
	"sprite-env/lib/adapters"

	"github.com/qmuntal/stateless"
)

// ManagedProcess defines the interface for processes that can be managed by ProcessState
type ManagedProcess interface {
	Start(ctx context.Context) error
	Stop()
	Signal(sig os.Signal)
	Events() <-chan adapters.ProcessEventType
}

// ProcessStateConfig holds the configuration for a process state manager
type ProcessStateConfig struct {
	InitialState string // Initial state, defaults to "Initializing"
	Process      ManagedProcess
	SystemState  *SystemState // Reference to system state for constraint validation
}

// ProcessState is a purely declarative intent processor for process states
// Following cursor rules: extends stateless.StateMachine
type ProcessState struct {
	*stateless.StateMachine
	config      ProcessStateConfig
	eventCtx    context.Context
	eventCancel context.CancelFunc
}

// NewProcessState creates a new process state manager with a managed process
// Initial state is "Initializing" as per TLA+ spec (unless overridden in config)
func NewProcessState(config ProcessStateConfig, monitors []lib.StateMonitor) *ProcessState {
	initialState := config.InitialState
	if initialState == "" {
		initialState = "Initializing" // Default per TLA+ spec
	}
	sm := stateless.NewStateMachine(initialState)

	eventCtx, eventCancel := context.WithCancel(context.Background())

	psm := &ProcessState{
		StateMachine: sm,
		config:       config,
		eventCtx:     eventCtx,
		eventCancel:  eventCancel,
	}

	// Attach monitors if provided
	if len(monitors) > 0 {
		sm.OnTransitioning(lib.CreateMonitorCallback("ProcessState", monitors))
	}

	// Configure states in execution sequence order

	// Initializing - can only go to Starting or Error (per TLA+ ComponentTransition)
	// Also allow Stopping for error recovery scenarios
	sm.Configure("Initializing").
		Permit("Starting", "Starting").
		Permit("Stopping", "Stopped").
		Permit("Error", "Error")

	// Starting - can go to Running or Error (per TLA+ ComponentTransition)
	sm.Configure("Starting").
		Permit("Running", "Running").
		Permit("Stopping", "Stopping").
		Permit("Error", "Error").
		OnEntry(psm.handleStarting)

	// Running - normal operation, can transition to many states
	sm.Configure("Running").
		Permit("Stopping", "Stopping").
		Permit("Signaling", "Signaling").
		Permit("Error", "Error").
		Permit("Exited", "Exited").
		Permit("Crashed", "Crashed").
		Permit("Killed", "Killed")

	// Stopping - graceful stop process
	sm.Configure("Stopping").
		Permit("Stopped", "Stopped").
		Permit("Error", "Error").
		Permit("Killed", "Killed").
		OnEntry(psm.handleStopping)

	// Signaling - process receiving signal
	sm.Configure("Signaling").
		Permit("Killed", "Killed").
		Permit("Stopped", "Stopped").
		Permit("Error", "Error").
		OnEntry(psm.handleSignaling)

	// Terminal states - no transitions out
	sm.Configure("Error")
	sm.Configure("Crashed")
	sm.Configure("Killed")
	sm.Configure("Exited")
	sm.Configure("Stopped")

	// Start listening for events from the process
	if config.Process != nil {
		go psm.listenForEvents()
	}

	return psm
}

// listenForEvents reads from the process events channel and triggers state transitions
func (psm *ProcessState) listenForEvents() {
	events := psm.config.Process.Events()
	for {
		select {
		case <-psm.eventCtx.Done():
			return
		case event := <-events:
			switch event {
			case adapters.ProcessStartingEvent:
				// Process reports it's starting - no state change needed, already in Starting
			case adapters.ProcessStartedEvent:
				// Process successfully started - transition to Running if not already there
				currentState := psm.MustState().(string)
				if currentState != "Running" {
					if err := psm.Fire("Running"); err != nil {
						panic(fmt.Sprintf("State machine error firing Running: %v", err))
					}
				}
			case adapters.ProcessStoppingEvent:
				// Process reports it's stopping - no state change needed, already in Stopping
			case adapters.ProcessStoppedEvent:
				// Process successfully stopped - transition to Stopped terminal state
				if err := psm.Fire("Stopped"); err != nil {
					panic(fmt.Sprintf("State machine error firing Stopped: %v", err))
				}
			case adapters.ProcessSignaledEvent:
				// Process received signal - depends on current state and signal type
				// For now, just acknowledge the signaling happened
			case adapters.ProcessExitedEvent:
				// Process exited normally
				if err := psm.Fire("Exited"); err != nil {
					panic(fmt.Sprintf("State machine error firing Exited: %v", err))
				}
			case adapters.ProcessRestartingEvent:
				// Process is restarting - transition back to Starting
				if err := psm.Fire("Starting"); err != nil {
					panic(fmt.Sprintf("State machine error firing Starting: %v", err))
				}
			case adapters.ProcessFailedEvent:
				// Process failed - transition to Error
				if err := psm.Fire("Error"); err != nil {
					panic(fmt.Sprintf("State machine error firing Error: %v", err))
				}
			}
		}
	}
}

// Close stops the event listener and cleans up resources
func (psm *ProcessState) Close() {
	// Close the underlying process first
	if psm.config.Process != nil {
		if closer, ok := psm.config.Process.(interface{ Close() error }); ok {
			closer.Close()
		}
	}

	// Cancel the event listener context
	if psm.eventCancel != nil {
		psm.eventCancel()
	}
}

// handleStarting is called when entering Starting state - should start the process
func (psm *ProcessState) handleStarting(ctx context.Context, args ...any) error {
	if psm.config.Process != nil {
		err := psm.config.Process.Start(ctx)
		if err != nil {
			// Start failed - fire Error transition
			if fireErr := psm.Fire("Error"); fireErr != nil {
				panic(fmt.Sprintf("State machine error firing Error: %v", fireErr))
			}
			return nil
		}
	}
	return nil
}

// handleStopping is called when entering Stopping state - should stop the process
func (psm *ProcessState) handleStopping(ctx context.Context, args ...any) error {
	if psm.config.Process != nil {
		psm.config.Process.Stop()
		// Note: We rely on the process to fire ProcessStoppedEvent when it's actually stopped
		// The state machine will transition to Stopped when that event is received
	} else {
		// No process to stop - transition directly to Stopped
		if err := psm.Fire("Stopped"); err != nil {
			panic(fmt.Sprintf("State machine error firing Stopped: %v", err))
		}
	}
	return nil
}

// handleSignaling is called when entering Signaling state - should send signal to process
func (psm *ProcessState) handleSignaling(ctx context.Context, args ...any) error {
	if psm.config.Process != nil {
		// Default to SIGTERM for signaling - could be made configurable
		psm.config.Process.Signal(os.Signal(os.Interrupt))
	}
	return nil
}

// Fire overrides the base Fire method to add constraint validation
func (psm *ProcessState) Fire(trigger string, args ...any) error {
	// Validate constraints before allowing state transitions
	if psm.config.SystemState != nil {
		currentSystemState := psm.config.SystemState.MustState().(string)

		switch trigger {
		case "Starting":
			// Process can only start when system is Ready or Running
			if currentSystemState != "Ready" && currentSystemState != "Running" {
				// Constraint violation - notify system and reject transition
				psm.config.SystemState.Fire("ProcessError")
				return fmt.Errorf("process cannot start when system state is %s", currentSystemState)
			}
		case "Running":
			// Process can only run when system is Ready or Running
			if currentSystemState != "Ready" && currentSystemState != "Running" {
				// Constraint violation - notify system and reject transition
				psm.config.SystemState.Fire("ProcessError")
				return fmt.Errorf("process cannot run when system state is %s", currentSystemState)
			}
		}
	}

	// If constraints pass, proceed with the transition
	return psm.StateMachine.Fire(trigger, args...)
}

// SetSystemState sets the system state reference for constraint validation
func (psm *ProcessState) SetSystemState(systemState *SystemState) {
	psm.config.SystemState = systemState
}
