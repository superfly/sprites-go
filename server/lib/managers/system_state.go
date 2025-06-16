package managers

import (
	"context"
	"fmt"
	"time"

	"github.com/qmuntal/stateless"
)

// SystemConfig holds the configuration for a system state manager
type SystemConfig struct {
	InitialState string // Initial state, defaults to "Initializing"
	ProcessState *ProcessState
	Components   []ManagedComponent
}

// SystemState is a purely declarative intent processor for system states
// Following cursor rules: extends stateless.StateMachine
type SystemState struct {
	*stateless.StateMachine
	config                SystemConfig
	componentGroupState   *ComponentGroupState
	externalExitChan      chan int       // External channel for sending exit codes to main app
	externalMonitors      []StateMonitor // Store external monitors for graceful shutdown
	componentGroupMonitor *systemMonitor // Internal monitor for component group events
	processMonitor        *systemMonitor // Internal monitor for process events
}

// Fire overrides the base Fire method
func (ssm *SystemState) Fire(trigger string, args ...any) error {
	err := ssm.StateMachine.Fire(trigger, args...)
	return err
}

// NewSystemState creates a new system state manager
// Initial state is "Initializing" as per TLA+ spec (unless overridden in config)
func NewSystemState(config SystemConfig, monitors []StateMonitor) *SystemState {
	initialState := config.InitialState
	if initialState == "" {
		initialState = "Initializing" // Default per TLA+ spec
	}
	sm := stateless.NewStateMachine(initialState)

	ssm := &SystemState{
		StateMachine:        sm,
		config:              config,
		componentGroupState: nil,
		externalMonitors:    monitors, // Store external monitors for graceful shutdown
	}

	// Attach monitors if provided
	if len(monitors) > 0 {
		sm.OnTransitioning(CreateMonitorCallback("SystemState", monitors))
	}

	// Add transition callback to detect terminal states
	sm.OnTransitioned(func(ctx context.Context, transition stateless.Transition) {
		if transition.Destination == "Error" {
			// Close external monitors gracefully first
			CloseMonitors(ssm.externalMonitors, 1*time.Second)

			// Close child managers to stop their goroutines
			if ssm.componentGroupState != nil {
				ssm.componentGroupState.Close()
			}
			if ssm.config.ProcessState != nil {
				ssm.config.ProcessState.Close()
			}

			// Signal that system has reached terminal error state with exit code 1
			if ssm.externalExitChan != nil {
				select {
				case ssm.externalExitChan <- 1:
				default:
					// Channel already has a value, ignore
				}
			}
		} else if transition.Destination == "Stopped" {
			// Close external monitors gracefully first
			CloseMonitors(ssm.externalMonitors, 1*time.Second)

			// Close child managers to stop their goroutines
			if ssm.componentGroupState != nil {
				ssm.componentGroupState.Close()
			}
			if ssm.config.ProcessState != nil {
				ssm.config.ProcessState.Close()
			}

			// Signal that system has reached terminal stopped state with exit code 0
			if ssm.externalExitChan != nil {
				select {
				case ssm.externalExitChan <- 0:
				default:
					// Channel already has a value, ignore
				}
			}
		}
	})

	// Create component group state manager if components provided
	var componentGroupState *ComponentGroupState
	if len(config.Components) > 0 {
		componentGroupConfig := ComponentGroupConfig{
			Components:        config.Components,
			ComponentMonitors: monitors, // Pass the external monitors to individual components
		}

		// Create component group monitor to translate component events to system events
		componentGroupMonitor := ssm.createComponentGroupMonitor()
		ssm.componentGroupMonitor = componentGroupMonitor.(*systemMonitor) // Store reference for cleanup

		// Pass both the componentGroupMonitor (for SystemState coordination)
		// and the external monitors (for TLA+ trace generation)
		allMonitors := append([]StateMonitor{componentGroupMonitor}, monitors...)
		componentGroupState = NewComponentGroupState(componentGroupConfig, allMonitors...)

		ssm.componentGroupState = componentGroupState
	}

	// Create process monitor to translate process events to system events
	if config.ProcessState != nil {
		// Set system state reference for constraint validation
		config.ProcessState.SetSystemState(ssm)

		processMonitor := ssm.createProcessMonitor()
		ssm.processMonitor = processMonitor.(*systemMonitor) // Store reference for cleanup
		// Attach the process monitor to the existing process state manager
		config.ProcessState.OnTransitioning(CreateMonitorCallback("ProcessState", []StateMonitor{processMonitor}))
	}

	// Configure system states based on TLA+ SystemState definition

	// Initializing - system starting up
	sm.Configure("Initializing").
		Permit("SystemStarting", "Starting").
		Permit("ProcessError", "Error").
		Permit("ProcessCrashed", "Error").
		Permit("ProcessKilled", "Error").
		Permit("ProcessExited", "Error")

	// Starting - system preparing, should start components
	sm.Configure("Starting").
		Permit("ComponentsRunning", "Ready").
		Permit("SystemReady", "Ready"). // For testing/manual control
		Permit("ComponentsErrorStopping", "ErrorRecovery").
		Permit("ComponentsError", "Error").
		Permit("ComponentsStopping", "Stopping").
		Permit("ProcessError", "Error").
		Permit("ProcessCrashed", "Error").
		Permit("ProcessKilled", "Error").
		Permit("ProcessExited", "Error").
		OnEntry(ssm.handleStarting)

	// Ready - components ready, process should start
	sm.Configure("Ready").
		Permit("ProcessRunning", "Running").
		Permit("ComponentsErrorStopping", "ErrorRecovery").
		Permit("ComponentsError", "Error").
		Permit("ComponentsStopping", "Stopping").
		Permit("ComponentsStopped", "Stopped").
		Permit("ProcessStopped", "Stopping").
		Permit("ProcessError", "ErrorRecovery").
		Permit("ProcessCrashed", "ErrorRecovery").
		Permit("ProcessKilled", "ErrorRecovery").
		Permit("ProcessExited", "ErrorRecovery").
		OnEntry(ssm.handleReady)

	// Running - full system operational (components ready + process running)
	sm.Configure("Running").
		Permit("ComponentsErrorStopping", "ErrorRecovery").
		Permit("ComponentsError", "Error").
		Permit("ComponentsStopping", "Stopping").
		Permit("ComponentsStopped", "Stopped").
		Permit("ProcessStopped", "Stopping").
		Permit("ProcessError", "ErrorRecovery").
		Permit("ProcessCrashed", "ErrorRecovery").
		Permit("ProcessKilled", "ErrorRecovery").
		Permit("ProcessExited", "ErrorRecovery")

	// ErrorRecovery - handling component failures
	sm.Configure("ErrorRecovery").
		Permit("ComponentsError", "Error"). // Allow transition to Error when components reach Error state
		Permit("ComponentsStopping", "Stopping").
		Permit("ProcessStopped", "Error"). // ONLY way to reach terminal Error
		Permit("ProcessError", "Error").
		Permit("ProcessCrashed", "Error").
		Permit("ProcessKilled", "Error").
		OnEntry(ssm.handleErrorRecovery)

	// Stopping - components/process stopping gracefully
	sm.Configure("Stopping").
		Permit("ComponentsStopped", "Stopped").
		Permit("ComponentsError", "Error").
		Permit("ProcessStopped", "Stopped").
		Permit("ProcessError", "Error").
		Permit("ProcessCrashed", "Error").
		Permit("ProcessKilled", "Error").
		Ignore("ComponentsStopping"). // Ignore redundant stopping events when already stopping
		OnEntry(ssm.handleStopping)

	// Terminal states - no transitions out (no OnEntry handlers needed now)
	sm.Configure("Error")   // Terminal error state
	sm.Configure("Stopped") // Terminal stopped state

	// TODO: Set up state coordination between managers using StateMonitor channels
	// This will replace the old callback-based approach

	return ssm
}

// handleStarting is called when entering Starting state - should start components
func (ssm *SystemState) handleStarting(ctx context.Context, args ...any) error {
	if ssm.componentGroupState != nil {
		err := ssm.componentGroupState.Fire("Starting")
		if err != nil {
			// Handle error by transitioning to Error state
			if fireErr := ssm.Fire("Error"); fireErr != nil {
				panic(fmt.Sprintf("State machine error firing Error: %v", fireErr))
			}
		}
	}
	return nil
}

// handleReady is called when entering Ready state - should start the process
func (ssm *SystemState) handleReady(ctx context.Context, args ...any) error {
	if ssm.config.ProcessState != nil {
		// Fire Starting on the process - synchronous because this is parent->child
		ssm.config.ProcessState.Fire("Starting")
	}
	return nil
}

// handleErrorRecovery is called when entering ErrorRecovery state - should stop process first
func (ssm *SystemState) handleErrorRecovery(ctx context.Context, args ...any) error {
	if ssm.config.ProcessState != nil {
		// Fire Stopping - the ProcessState will handle whether it needs to actually stop a process or not
		ssm.config.ProcessState.Fire("Stopping")
	}
	return nil
}

// handleStopping is called when entering Stopping state - coordinate component shutdown
func (ssm *SystemState) handleStopping(ctx context.Context, args ...any) error {
	if ssm.componentGroupState != nil {
		// Stop the component group - synchronous because this is parent->child
		ssm.componentGroupState.Fire("Stopping")
	} else {
		// No components to coordinate, can transition directly to stopped
		if err := ssm.Fire("ComponentsStopped"); err != nil {
			panic(fmt.Sprintf("State machine error firing ComponentsStopped: %v", err))
		}
	}
	return nil
}

// createComponentGroupMonitor creates a monitor to translate component group events to system events
func (ssm *SystemState) createComponentGroupMonitor() StateMonitor {
	events := make(chan StateTransition, 100) // Buffered channel

	// Start goroutine to process component group state changes
	go func() {
		for transition := range events {
			// Check if system is in terminal state - if so, ignore component events
			currentSystemState := ssm.MustState().(string)
			if currentSystemState == "Error" || currentSystemState == "Stopped" {
				// System is in terminal state, ignore component events
				continue
			}

			// Also check if component group is in terminal state - if so, ignore events
			if ssm.componentGroupState != nil {
				currentComponentState := ssm.componentGroupState.MustState().(string)
				if currentComponentState == "Error" || currentComponentState == "Stopped" {
					// Component group is in terminal state, ignore events
					continue
				}
			}

			switch transition.To {
			case "Running":
				if err := ssm.Fire("ComponentsRunning"); err != nil {
					panic(fmt.Sprintf("State machine error firing ComponentsRunning: %v", err))
				}
			case "ErrorStopping":
				if err := ssm.Fire("ComponentsErrorStopping"); err != nil {
					panic(fmt.Sprintf("State machine error firing ComponentsErrorStopping: %v", err))
				}
			case "Error":
				if err := ssm.Fire("ComponentsError"); err != nil {
					panic(fmt.Sprintf("State machine error firing ComponentsError: %v", err))
				}
			case "Stopping":
				if err := ssm.Fire("ComponentsStopping"); err != nil {
					panic(fmt.Sprintf("State machine error firing ComponentsStopping: %v", err))
				}
			case "Stopped":
				if err := ssm.Fire("ComponentsStopped"); err != nil {
					panic(fmt.Sprintf("State machine error firing ComponentsStopped: %v", err))
				}

			}
		}
	}()

	return &systemMonitor{events: events}
}

// createProcessMonitor creates a monitor to translate process events to system events
func (ssm *SystemState) createProcessMonitor() StateMonitor {
	events := make(chan StateTransition, 100) // Buffered channel

	// Start goroutine to process process state changes
	go func() {
		for transition := range events {
			// Check if system is in terminal state - if so, ignore process events
			currentSystemState := ssm.MustState().(string)
			if currentSystemState == "Error" || currentSystemState == "Stopped" {
				// System is in terminal state, ignore process events
				continue
			}

			switch transition.To {
			case "Starting":
				// Process starting - no system state change needed for Starting
			case "Running":
				// Process successfully started - system transitions to Running (full system operational)
				if err := ssm.Fire("ProcessRunning"); err != nil {
					// If ProcessRunning is not allowed from current state, treat as constraint violation
					if err := ssm.Fire("ProcessError"); err != nil {
						panic(fmt.Sprintf("State machine error firing ProcessError: %v", err))
					}
				}
			case "Error":
				if err := ssm.Fire("ProcessError"); err != nil {
					panic(fmt.Sprintf("State machine error firing ProcessError: %v", err))
				}
			case "Crashed":
				if err := ssm.Fire("ProcessCrashed"); err != nil {
					panic(fmt.Sprintf("State machine error firing ProcessCrashed: %v", err))
				}
			case "Killed":
				if err := ssm.Fire("ProcessKilled"); err != nil {
					panic(fmt.Sprintf("State machine error firing ProcessKilled: %v", err))
				}
			case "Exited":
				if err := ssm.Fire("ProcessExited"); err != nil {
					panic(fmt.Sprintf("State machine error firing ProcessExited: %v", err))
				}
			case "Stopping":
				// Don't report intermediate Stopping state - wait for final Stopped state
			case "Stopped":
				if err := ssm.Fire("ProcessStopped"); err != nil {
					panic(fmt.Sprintf("State machine error firing ProcessStopped: %v", err))
				}

			}
		}
	}()

	return &systemMonitor{events: events}
}

// systemMonitor implements StateMonitor interface for internal system coordination
type systemMonitor struct {
	events chan StateTransition
}

func (sm *systemMonitor) Events() chan<- StateTransition {
	return sm.events
}

// Close closes the monitor channel to stop the associated goroutine
func (sm *systemMonitor) Close() error {
	if sm.events != nil {
		close(sm.events)
		sm.events = nil
	}
	return nil
}

// Close stops all child managers and monitor goroutines
func (ssm *SystemState) Close() {
	// Close internal monitors first to stop their goroutines
	if ssm.componentGroupMonitor != nil {
		ssm.componentGroupMonitor.Close()
		ssm.componentGroupMonitor = nil
	}
	if ssm.processMonitor != nil {
		ssm.processMonitor.Close()
		ssm.processMonitor = nil
	}

	// Close child managers
	if ssm.componentGroupState != nil {
		ssm.componentGroupState.Close()
	}
	if ssm.config.ProcessState != nil {
		ssm.config.ProcessState.Close()
	}
}

// SetExitChannel sets an external channel to receive exit codes when terminal states are reached
func (ssm *SystemState) SetExitChannel(exitChan chan int) {
	ssm.externalExitChan = exitChan
}
