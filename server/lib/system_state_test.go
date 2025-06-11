package lib

import (
	"context"
	"fmt"
	"testing"
	"time"

	"github.com/qmuntal/stateless"
)

// waitForSystemState waits for the system state machine to reach the expected state
func waitForSystemState(ssm *SystemState, expected SystemStateType, timeout time.Duration) bool {
	deadline := time.Now().Add(timeout)
	for time.Now().Before(deadline) {
		if ssm.GetState() == expected {
			return true
		}
		time.Sleep(time.Millisecond)
	}
	return false
}

// Note: Helper functions completeComponentStartup and completeComponentShutdown
// are already defined elsewhere in this file or imported

// Test complete system lifecycle sequences from TLA+ spec
func TestSystemStateMachine_TLASpecSequences(t *testing.T) {
	t.Run("Complete_Startup_Sequence", func(t *testing.T) {
		// Create test dependencies
		processSM, fakeProcess := NewTestableProcessStateMachine()
		componentSetSM, fakeComponents := NewTestableComponentSetStateMachine()

		// Clean up
		defer fakeProcess.Close()
		defer fakeComponents["db"].Close()
		defer fakeComponents["fs"].Close()

		// Create system state machine
		ssm := NewSystemState(componentSetSM, processSM)

		// Start system state machine

		// Should start in Initializing state
		if ssm.GetState() != SystemStateInitializing {
			t.Errorf("Expected Initializing initial state, got %s", ssm.GetState())
		}

		// System automatically starts components, drive fake components through startup
		time.Sleep(10 * time.Millisecond) // Allow system to start components

		// Drive fake components through their startup sequence
		for _, fake := range fakeComponents {
			completeComponentStartup(fake)
		}

		// Complete process startup (process should be in Starting state after system reaches Ready)
		fakeProcess.EmitEvent(EventStarted)

		// Wait for system to reach Running state through reactive coordination
		if !waitForSystemState(ssm, SystemStateRunning, 2000*time.Millisecond) {
			t.Errorf("Expected Running after component startup, got %s", ssm.GetState())
			t.Logf("Final - System state: %s, ComponentSet state: %s, Process state: %s",
				ssm.GetState(), ssm.GetComponentSetState(), ssm.GetProcessState())
		}
	})

	t.Run("Complete_Shutdown_Sequence", func(t *testing.T) {
		// Create test dependencies
		processSM, fakeProcess := NewTestableProcessStateMachine()
		componentSetSM, fakeComponents := NewTestableComponentSetStateMachine()

		// Clean up
		defer fakeProcess.Close()
		defer fakeComponents["db"].Close()
		defer fakeComponents["fs"].Close()

		// Track all state transitions
		var transitions []string

		// Create system state machine
		ssm := NewSystemState(componentSetSM, processSM)

		// Add callbacks to track all state transitions
		ssm.OnTransitioned(func(ctx context.Context, transition stateless.Transition) {
			msg := fmt.Sprintf("SystemStateMachine: %v -> %v", transition.Source, transition.Destination)
			transitions = append(transitions, msg)
			t.Logf("SSM STATE CHANGE: %s", msg)
		})

		processSM.OnTransitioned(func(ctx context.Context, transition stateless.Transition) {
			msg := fmt.Sprintf("ProcessStateMachine: %v -> %v", transition.Source, transition.Destination)
			transitions = append(transitions, msg)
			t.Logf("PROCESS STATE CHANGE: %s", msg)
		})

		componentSetSM.OnTransitioned(func(ctx context.Context, transition stateless.Transition) {
			msg := fmt.Sprintf("ComponentSetStateMachine: %v -> %v", transition.Source, transition.Destination)
			transitions = append(transitions, msg)
			t.Logf("COMPONENT SET STATE CHANGE: %s", msg)
		})

		// Start and get to running state first
		t.Logf("Starting system...")

		// System automatically coordinates based on component readiness
		// No manual triggers needed

		// Complete startup
		t.Logf("Starting components...")
		fakeComponents["db"].EmitEvent(ComponentStarting)
		fakeComponents["fs"].EmitEvent(ComponentStarting)
		fakeComponents["db"].EmitEvent(ComponentStarted)
		fakeComponents["fs"].EmitEvent(ComponentStarted)
		fakeComponents["db"].EmitEvent(ComponentReady)
		fakeComponents["fs"].EmitEvent(ComponentReady)
		fakeProcess.EmitEvent(EventStarted)
		waitForSystemState(ssm, SystemStateRunning, 500*time.Millisecond)

		t.Logf("System running state: %s", ssm.GetState())
		t.Logf("Component set state: %s", ssm.GetComponentSetState())
		t.Logf("Process state: %s", ssm.GetProcessState())

		// Request shutdown
		t.Logf("Requesting shutdown...")
		if err := ssm.Fire(SystemTriggerShutdownRequested); err != nil {
			t.Fatalf("Failed to request shutdown: %v", err)
		}

		// Should transition to ShuttingDown
		if !waitForSystemState(ssm, SystemStateShuttingDown, 500*time.Millisecond) {
			t.Errorf("Expected ShuttingDown after shutdown request, got %s", ssm.GetState())
		}

		t.Logf("After shutdown request - System state: %s", ssm.GetState())
		t.Logf("After shutdown request - Component set state: %s", ssm.GetComponentSetState())
		t.Logf("After shutdown request - Process state: %s", ssm.GetProcessState())

		// Complete component shutdown
		t.Logf("Shutting down components...")
		fakeComponents["db"].EmitEvent(ComponentStopping)
		fakeComponents["fs"].EmitEvent(ComponentStopping)
		time.Sleep(10 * time.Millisecond)
		t.Logf("After stopping events - Component set state: %s", ssm.GetComponentSetState())

		fakeComponents["db"].EmitEvent(ComponentStopped)
		fakeComponents["fs"].EmitEvent(ComponentStopped)
		time.Sleep(10 * time.Millisecond)
		t.Logf("After stopped events - Component set state: %s", ssm.GetComponentSetState())
		t.Logf("After component shutdown - System state: %s", ssm.GetState())

		// Complete process shutdown
		t.Logf("Shutting down process...")
		fakeProcess.EmitEvent(EventStopping)
		time.Sleep(10 * time.Millisecond)
		t.Logf("After process stopping - Process state: %s", ssm.GetProcessState())

		fakeProcess.EmitEvent(EventStopped)
		time.Sleep(10 * time.Millisecond)
		t.Logf("After process stopped - Process state: %s", ssm.GetProcessState())
		t.Logf("After process shutdown - System state: %s", ssm.GetState())

		// Wait a bit to see if any additional transitions happen
		time.Sleep(100 * time.Millisecond)
		t.Logf("After wait - System state: %s", ssm.GetState())

		// Should reach Shutdown state
		if !waitForSystemState(ssm, SystemStateShutdown, 500*time.Millisecond) {
			t.Errorf("Expected Shutdown after shutdown sequence, got %s", ssm.GetState())
			t.Logf("Final state - System: %s, ComponentSet: %s, Process: %s",
				ssm.GetState(), ssm.GetComponentSetState(), ssm.GetProcessState())
			t.Logf("All transitions: %v", transitions)
		}

	})

	t.Run("Complete_Checkpoint_Sequence", func(t *testing.T) {
		// Create test dependencies
		processSM, fakeProcess := NewTestableProcessStateMachine()
		componentSetSM, fakeComponents := NewTestableComponentSetStateMachine()

		// Clean up
		defer fakeProcess.Close()
		defer fakeComponents["db"].Close()
		defer fakeComponents["fs"].Close()

		// Create system state machine
		ssm := NewSystemState(componentSetSM, processSM)

		// Start and get to running state first

		// System automatically starts components, drive them through startup
		time.Sleep(10 * time.Millisecond) // Allow system to start components

		// Drive fake components through their startup sequence
		for _, fake := range fakeComponents {
			completeComponentStartup(fake)
		}

		// Complete process startup
		fakeProcess.EmitEvent(EventStarted)

		// Wait for system to reach Running state before checkpoint
		if !waitForSystemState(ssm, SystemStateRunning, 2000*time.Millisecond) {
			t.Fatalf("System should be Running before checkpoint, got %s", ssm.GetState())
		}

		// Request checkpoint
		if err := ssm.Fire(SystemTriggerCheckpointRequested); err != nil {
			t.Fatalf("Failed to request checkpoint: %v", err)
		}

		// Should transition to Checkpointing
		if !waitForSystemState(ssm, SystemStateCheckpointing, 500*time.Millisecond) {
			t.Errorf("Expected Checkpointing after checkpoint request, got %s", ssm.GetState())
		}

		// Verify checkpoint flag
		if ssm.GetState() != SystemStateCheckpointing {
			t.Error("Expected checkpoint in progress flag to be true")
		}

		// Wait for checkpoint to complete (automatic return to Running)
		if !waitForSystemState(ssm, SystemStateRunning, 300*time.Millisecond) {
			t.Errorf("Expected Running after checkpoint completion, got %s", ssm.GetState())
		}
	})

	t.Run("Complete_Restore_Sequence", func(t *testing.T) {
		// Create test dependencies
		processSM, fakeProcess := NewTestableProcessStateMachine()
		componentSetSM, fakeComponents := NewTestableComponentSetStateMachine()

		// Clean up
		defer fakeProcess.Close()
		defer fakeComponents["db"].Close()
		defer fakeComponents["fs"].Close()

		// Create system state machine
		ssm := NewSystemState(componentSetSM, processSM)

		// Start and get to running state first

		// System automatically starts components, drive them through startup
		time.Sleep(10 * time.Millisecond) // Allow system to start components

		// Drive fake components through their startup sequence
		for _, fake := range fakeComponents {
			completeComponentStartup(fake)
		}

		// Complete process startup
		fakeProcess.EmitEvent(EventStarted)

		// Wait for system to reach Running state before restore
		if !waitForSystemState(ssm, SystemStateRunning, 2000*time.Millisecond) {
			t.Fatalf("System should be Running before restore, got %s", ssm.GetState())
		}

		// Request restore
		if err := ssm.Fire(SystemTriggerRestoreRequested); err != nil {
			t.Fatalf("Failed to request restore: %v", err)
		}

		// Should transition to Restoring
		if !waitForSystemState(ssm, SystemStateRestoring, 500*time.Millisecond) {
			t.Errorf("Expected Restoring after restore request, got %s", ssm.GetState())
		}

		// Verify restore flag
		if ssm.GetState() != SystemStateRestoring {
			t.Error("Expected restore in progress flag to be true")
		}

		// Wait for restore to complete and components to transition to Starting
		time.Sleep(150 * time.Millisecond)

		// Complete component startup from Starting state (no ComponentStarting needed)
		fakeComponents["db"].EmitEvent(ComponentStarted)
		fakeComponents["fs"].EmitEvent(ComponentStarted)
		fakeComponents["db"].EmitEvent(ComponentReady)
		fakeComponents["fs"].EmitEvent(ComponentReady)

		// Should return to Running
		if !waitForSystemState(ssm, SystemStateRunning, 300*time.Millisecond) {
			t.Errorf("Expected Running after restore completion, got %s", ssm.GetState())
		}

		// Verify restore flag cleared
		if ssm.GetState() == SystemStateRestoring {
			t.Error("Expected restore in progress flag to be false after completion")
		}
	})

	t.Run("Process_Waits_For_ComponentSet_Coordination", func(t *testing.T) {
		// Create test dependencies
		processSM, fakeProcess := NewTestableProcessStateMachine()
		componentSetSM, fakeComponents := NewTestableComponentSetStateMachine()

		// Clean up
		defer fakeProcess.Close()
		defer fakeComponents["db"].Close()
		defer fakeComponents["fs"].Close()

		// Create system state machine
		ssm := NewSystemState(componentSetSM, processSM)

		// Start system state machine

		// System automatically coordinates based on component readiness
		// No manual triggers needed

		// Start components transitioning
		fakeComponents["db"].EmitEvent(ComponentStarting)
		fakeComponents["fs"].EmitEvent(ComponentStarting)
		time.Sleep(10 * time.Millisecond) // Allow components to transition

		// At this point, process should NOT be Running yet because components aren't ready
		if ssm.GetProcessState() == ProcessStateRunning {
			t.Error("ProcessStateMachine should NOT be Running before ComponentSetStateMachine is Running")
		}

		// Verify ComponentSetStateMachine is still Initializing (components not all running yet)
		if ssm.GetComponentSetState() == ComponentSetStateRunning {
			t.Error("ComponentSetStateMachine should not be Running yet - components not all ready")
		}

		// Now complete component startup to get ComponentSetStateMachine to Running
		fakeComponents["db"].EmitEvent(ComponentStarted)
		fakeComponents["fs"].EmitEvent(ComponentStarted)
		fakeComponents["db"].EmitEvent(ComponentReady)
		fakeComponents["fs"].EmitEvent(ComponentReady)
		time.Sleep(50 * time.Millisecond) // Allow ComponentSetStateMachine to transition

		// Verify ComponentSetStateMachine reaches Running first
		if ssm.GetComponentSetState() != ComponentSetStateRunning {
			t.Error("ComponentSetStateMachine should be Running after all components are ready")
		}

		// Now the SystemStateMachine should have requested the process to start
		// Complete the process startup sequence
		fakeProcess.EmitEvent(EventStarted)
		time.Sleep(50 * time.Millisecond) // Allow process to reach Running

		if ssm.GetProcessState() != ProcessStateRunning {
			t.Error("ProcessStateMachine should be Running after ComponentSetStateMachine is Running")
		}

		// Final system state should be Running
		if !waitForSystemState(ssm, SystemStateRunning, 200*time.Millisecond) {
			t.Errorf("Expected system to reach Running state, got %s", ssm.GetState())
		}
	})

	t.Run("ProcessStateMachine_Waits_For_SystemReady", func(t *testing.T) {
		// Create test dependencies
		processSM, fakeProcess := NewTestableProcessStateMachine()
		componentSetSM, fakeComponents := NewTestableComponentSetStateMachine()

		// Clean up
		defer fakeProcess.Close()
		defer fakeComponents["db"].Close()
		defer fakeComponents["fs"].Close()

		// Create system state machine
		ssm := NewSystemState(componentSetSM, processSM)

		// Start system state machine

		// System automatically coordinates based on component readiness
		// No manual triggers needed - process should NOT start until components ready

		// At this point, ProcessStateMachine should still be Initializing
		if ssm.GetProcessState() != ProcessStateInitializing {
			t.Errorf("ProcessStateMachine should still be Initializing, got %s", ssm.GetProcessState())
		}

		// Complete component startup to trigger system Ready
		fakeComponents["db"].EmitEvent(ComponentStarting)
		fakeComponents["fs"].EmitEvent(ComponentStarting)
		fakeComponents["db"].EmitEvent(ComponentStarted)
		fakeComponents["fs"].EmitEvent(ComponentStarted)
		fakeComponents["db"].EmitEvent(ComponentReady)
		fakeComponents["fs"].EmitEvent(ComponentReady)

		// Wait for system to process component changes
		time.Sleep(50 * time.Millisecond)

		// SystemStateMachine should now be in Ready state (public API)
		currentState := ssm.GetState()
		if currentState != SystemStateReady {
			t.Errorf("SystemStateMachine should be Ready after components ready, got %s", currentState)
		}

		// NOW ProcessStateMachine should have transitioned to Starting
		if ssm.GetProcessState() != ProcessStateStarting {
			t.Errorf("ProcessStateMachine should be Starting after system Ready, got %s", ssm.GetProcessState())
		}

		// Complete process startup to reach Running
		fakeProcess.EmitEvent(EventStarted)

		// Should reach Running state
		if !waitForSystemState(ssm, SystemStateRunning, 200*time.Millisecond) {
			t.Errorf("Expected Running after process startup, got %s", ssm.GetState())
		}
	})
}

// Test reactive state determination logic
func TestSystemStateMachine_DetermineOverallState(t *testing.T) {
	t.Run("Initializing_To_Ready_When_ComponentSet_Running", func(t *testing.T) {
		// Create test dependencies
		processSM, fakeProcess := NewTestableProcessStateMachine()
		componentSetSM, fakeComponents := NewTestableComponentSetStateMachine()

		// Clean up
		defer fakeProcess.Close()
		defer fakeComponents["db"].Close()
		defer fakeComponents["fs"].Close()

		// Create system state machine (starts in Initializing)
		ssm := NewSystemState(componentSetSM, processSM)

		// System should start in Initializing
		if ssm.GetState() != SystemStateInitializing {
			t.Errorf("Expected Initializing initially, got %s", ssm.GetState())
		}

		// Complete component startup to get ComponentSet to Running
		for _, fake := range fakeComponents {
			completeComponentStartup(fake)
		}

		// System should automatically transition Initializing -> Ready
		if !waitForSystemState(ssm, SystemStateReady, 500*time.Millisecond) {
			t.Errorf("Expected Ready after ComponentSet becomes Running, got %s", ssm.GetState())
		}
	})

	t.Run("Ready_To_Running_When_Both_Dependencies_Ready", func(t *testing.T) {
		// Create test dependencies
		processSM, fakeProcess := NewTestableProcessStateMachine()
		componentSetSM, fakeComponents := NewTestableComponentSetStateMachine()

		// Clean up
		defer fakeProcess.Close()
		defer fakeComponents["db"].Close()
		defer fakeComponents["fs"].Close()

		// Create system state machine
		ssm := NewSystemState(componentSetSM, processSM)

		// Get to Ready state first
		for _, fake := range fakeComponents {
			completeComponentStartup(fake)
		}
		waitForSystemState(ssm, SystemStateReady, 500*time.Millisecond)

		// Process should have started automatically, complete its startup
		fakeProcess.EmitEvent(EventStarted)

		// System should automatically transition Ready -> Running
		if !waitForSystemState(ssm, SystemStateRunning, 500*time.Millisecond) {
			t.Errorf("Expected Running after both dependencies ready, got %s", ssm.GetState())
		}
	})

	t.Run("ShuttingDown_To_Shutdown_When_Dependencies_Complete", func(t *testing.T) {
		// Create test dependencies
		processSM, fakeProcess := NewTestableProcessStateMachine()
		componentSetSM, fakeComponents := NewTestableComponentSetStateMachine()

		// Clean up
		defer fakeProcess.Close()
		defer fakeComponents["db"].Close()
		defer fakeComponents["fs"].Close()

		// Create system state machine and get to Running
		ssm := NewSystemState(componentSetSM, processSM)

		for _, fake := range fakeComponents {
			completeComponentStartup(fake)
		}
		fakeProcess.EmitEvent(EventStarted)
		waitForSystemState(ssm, SystemStateRunning, 500*time.Millisecond)

		// Request shutdown
		ssm.Fire(SystemTriggerShutdownRequested)
		waitForSystemState(ssm, SystemStateShuttingDown, 500*time.Millisecond)

		// Complete shutdown sequence
		for _, fake := range fakeComponents {
			fake.EmitEvent(ComponentStopping)
			fake.EmitEvent(ComponentStopped)
		}
		fakeProcess.EmitEvent(EventStopping)
		fakeProcess.EmitEvent(EventStopped)

		// System should automatically transition ShuttingDown -> Shutdown
		if !waitForSystemState(ssm, SystemStateShutdown, 500*time.Millisecond) {
			t.Errorf("Expected Shutdown after dependencies shutdown, got %s", ssm.GetState())
		}
	})

	t.Run("Checkpointing_To_Running_When_Complete", func(t *testing.T) {
		// Create test dependencies
		processSM, fakeProcess := NewTestableProcessStateMachine()
		componentSetSM, fakeComponents := NewTestableComponentSetStateMachine()

		// Clean up
		defer fakeProcess.Close()
		defer fakeComponents["db"].Close()
		defer fakeComponents["fs"].Close()

		// Create system state machine and get to Running
		ssm := NewSystemState(componentSetSM, processSM)

		for _, fake := range fakeComponents {
			completeComponentStartup(fake)
		}
		fakeProcess.EmitEvent(EventStarted)
		waitForSystemState(ssm, SystemStateRunning, 500*time.Millisecond)

		// Request checkpoint
		ssm.Fire(SystemTriggerCheckpointRequested)
		waitForSystemState(ssm, SystemStateCheckpointing, 500*time.Millisecond)

		// ComponentSet should automatically return to Running after checkpoint
		// (checkpoint operation completes automatically in test)
		if !waitForSystemState(ssm, SystemStateRunning, 500*time.Millisecond) {
			t.Errorf("Expected Running after checkpoint completes, got %s", ssm.GetState())
		}
	})

	t.Run("Restoring_To_Running_When_Complete", func(t *testing.T) {
		// Create test dependencies
		processSM, fakeProcess := NewTestableProcessStateMachine()
		componentSetSM, fakeComponents := NewTestableComponentSetStateMachine()

		// Clean up
		defer fakeProcess.Close()
		defer fakeComponents["db"].Close()
		defer fakeComponents["fs"].Close()

		// Create system state machine and get to Running
		ssm := NewSystemState(componentSetSM, processSM)

		for _, fake := range fakeComponents {
			completeComponentStartup(fake)
		}
		fakeProcess.EmitEvent(EventStarted)
		waitForSystemState(ssm, SystemStateRunning, 500*time.Millisecond)

		// Request restore
		ssm.Fire(SystemTriggerRestoreRequested)
		waitForSystemState(ssm, SystemStateRestoring, 500*time.Millisecond)

		// Wait for restore to complete and components to transition to Starting
		time.Sleep(150 * time.Millisecond)

		// Complete component startup after restore
		for _, fake := range fakeComponents {
			fake.EmitEvent(ComponentStarted)
			fake.EmitEvent(ComponentReady)
		}

		// System should automatically transition Restoring -> Running
		if !waitForSystemState(ssm, SystemStateRunning, 500*time.Millisecond) {
			t.Errorf("Expected Running after restore completes, got %s", ssm.GetState())
		}
	})
}

// Test error type determination based on failure source
func TestSystemStateMachine_ErrorTypeDetermination(t *testing.T) {
	t.Run("Process_Error_Sets_ProcessError_Type", func(t *testing.T) {
		// Create test dependencies
		processSM, fakeProcess := NewTestableProcessStateMachine()
		componentSetSM, fakeComponents := NewTestableComponentSetStateMachine()

		// Clean up
		defer fakeProcess.Close()
		defer fakeComponents["db"].Close()
		defer fakeComponents["fs"].Close()

		// Create system state machine and get to Running
		ssm := NewSystemState(componentSetSM, processSM)

		for _, fake := range fakeComponents {
			completeComponentStartup(fake)
		}
		fakeProcess.EmitEvent(EventStarted)
		waitForSystemState(ssm, SystemStateRunning, 500*time.Millisecond)

		// Cause process error
		fakeProcess.EmitEvent(EventFailed)

		// System should transition to Error state
		waitForSystemState(ssm, SystemStateError, 500*time.Millisecond)

		// Error type should be ProcessError
		if ssm.GetErrorType() != ErrorTypeProcessError {
			t.Errorf("Expected ProcessError error type, got %s", ssm.GetErrorType())
		}
	})

	t.Run("Process_Crash_Sets_ProcessCrash_Type", func(t *testing.T) {
		// Create test dependencies
		processSM, fakeProcess := NewTestableProcessStateMachine()
		componentSetSM, fakeComponents := NewTestableComponentSetStateMachine()

		// Clean up
		defer fakeProcess.Close()
		defer fakeComponents["db"].Close()
		defer fakeComponents["fs"].Close()

		// Create system state machine and get to Running
		ssm := NewSystemState(componentSetSM, processSM)

		for _, fake := range fakeComponents {
			completeComponentStartup(fake)
		}
		fakeProcess.EmitEvent(EventStarted)
		waitForSystemState(ssm, SystemStateRunning, 500*time.Millisecond)

		// Simulate process crash - EventExited leads to ProcessStateCrashed
		fakeProcess.EmitEvent(EventExited)

		// System should transition to Error state
		waitForSystemState(ssm, SystemStateError, 500*time.Millisecond)

		// Error type should be ProcessCrash
		if ssm.GetErrorType() != ErrorTypeProcessCrash {
			t.Errorf("Expected ProcessCrash error type, got %s", ssm.GetErrorType())
		}
	})

	t.Run("Process_Killed_Sets_ProcessKilled_Type", func(t *testing.T) {
		// Create test dependencies
		processSM, fakeProcess := NewTestableProcessStateMachine()
		componentSetSM, fakeComponents := NewTestableComponentSetStateMachine()

		// Clean up
		defer fakeProcess.Close()
		defer fakeComponents["db"].Close()
		defer fakeComponents["fs"].Close()

		// Create system state machine and get to Running
		ssm := NewSystemState(componentSetSM, processSM)

		for _, fake := range fakeComponents {
			completeComponentStartup(fake)
		}
		fakeProcess.EmitEvent(EventStarted)
		waitForSystemState(ssm, SystemStateRunning, 500*time.Millisecond)

		// Simulate process being killed - proper signal flow
		processSM.Fire(TriggerSignal)        // Go to Signaling state, sets lastSignal to SIGKILL
		fakeProcess.EmitEvent(EventSignaled) // Process reports it was killed

		// System should transition to Error state
		waitForSystemState(ssm, SystemStateError, 500*time.Millisecond)

		// Error type should be ProcessKilled
		if ssm.GetErrorType() != ErrorTypeProcessKilled {
			t.Errorf("Expected ProcessKilled error type, got %s", ssm.GetErrorType())
		}
	})

	t.Run("ComponentSet_Error_Sets_DBError_Type", func(t *testing.T) {
		// Create test dependencies
		processSM, fakeProcess := NewTestableProcessStateMachine()
		componentSetSM, fakeComponents := NewTestableComponentSetStateMachine()

		// Clean up
		defer fakeProcess.Close()
		defer fakeComponents["db"].Close()
		defer fakeComponents["fs"].Close()

		// Create system state machine and get to Running
		ssm := NewSystemState(componentSetSM, processSM)

		for _, fake := range fakeComponents {
			completeComponentStartup(fake)
		}
		fakeProcess.EmitEvent(EventStarted)
		waitForSystemState(ssm, SystemStateRunning, 500*time.Millisecond)

		// Cause component failure to trigger ComponentSet error
		fakeComponents["db"].EmitEvent(ComponentFailed)

		// System should transition to Error state
		waitForSystemState(ssm, SystemStateError, 500*time.Millisecond)

		// Error type should be DBError (generic component error)
		if ssm.GetErrorType() != ErrorTypeDBError {
			t.Errorf("Expected DBError error type, got %s", ssm.GetErrorType())
		}
	})

	t.Run("Error_Type_None_Initially", func(t *testing.T) {
		// Create test dependencies
		processSM, fakeProcess := NewTestableProcessStateMachine()
		componentSetSM, fakeComponents := NewTestableComponentSetStateMachine()

		// Clean up
		defer fakeProcess.Close()
		defer fakeComponents["db"].Close()
		defer fakeComponents["fs"].Close()

		// Create system state machine
		ssm := NewSystemState(componentSetSM, processSM)

		// Initially error type should be None
		if ssm.GetErrorType() != ErrorTypeNone {
			t.Errorf("Expected None error type initially, got %s", ssm.GetErrorType())
		}

		// Complete startup to Running state
		for _, fake := range fakeComponents {
			completeComponentStartup(fake)
		}
		fakeProcess.EmitEvent(EventStarted)
		waitForSystemState(ssm, SystemStateRunning, 500*time.Millisecond)

		// Should still be None in running state
		if ssm.GetErrorType() != ErrorTypeNone {
			t.Errorf("Expected None error type in running state, got %s", ssm.GetErrorType())
		}
	})
}

// Test that final states reject further transitions
func TestSystemStateMachine_FinalStates(t *testing.T) {
	t.Run("Shutdown_State_Rejects_Transitions", func(t *testing.T) {
		// Create test dependencies
		processSM, fakeProcess := NewTestableProcessStateMachine()
		componentSetSM, fakeComponents := NewTestableComponentSetStateMachine()

		// Clean up
		defer fakeProcess.Close()
		defer fakeComponents["db"].Close()
		defer fakeComponents["fs"].Close()

		// Create system state machine
		ssm := NewSystemState(componentSetSM, processSM)

		// Get to running state first, then shut down to reach final state

		// System automatically coordinates based on component readiness
		// No manual triggers needed

		// Complete startup
		fakeComponents["db"].EmitEvent(ComponentStarting)
		fakeComponents["fs"].EmitEvent(ComponentStarting)
		fakeComponents["db"].EmitEvent(ComponentStarted)
		fakeComponents["fs"].EmitEvent(ComponentStarted)
		fakeComponents["db"].EmitEvent(ComponentReady)
		fakeComponents["fs"].EmitEvent(ComponentReady)
		fakeProcess.EmitEvent(EventStarted)
		waitForSystemState(ssm, SystemStateRunning, 500*time.Millisecond)

		// Request shutdown to reach final state
		ssm.Fire(SystemTriggerShutdownRequested)

		// Complete shutdown sequence
		fakeComponents["db"].EmitEvent(ComponentStopping)
		fakeComponents["fs"].EmitEvent(ComponentStopping)
		fakeComponents["db"].EmitEvent(ComponentStopped)
		fakeComponents["fs"].EmitEvent(ComponentStopped)
		fakeProcess.EmitEvent(EventStopping)
		fakeProcess.EmitEvent(EventStopped)

		// Wait for final shutdown state
		waitForSystemState(ssm, SystemStateShutdown, 500*time.Millisecond)

		// Now try to transition from final state - should be rejected
		err := ssm.Fire(SystemTriggerStart)
		if err == nil {
			t.Error("Shutdown final state should reject transitions")
		}
	})

	t.Run("Error_State_Rejects_Transitions", func(t *testing.T) {
		// Create test dependencies
		processSM, fakeProcess := NewTestableProcessStateMachine()
		componentSetSM, fakeComponents := NewTestableComponentSetStateMachine()

		// Clean up
		defer fakeProcess.Close()
		defer fakeComponents["db"].Close()
		defer fakeComponents["fs"].Close()

		// Create system state machine
		ssm := NewSystemState(componentSetSM, processSM)

		// Get to running state first, then cause an error to reach error state

		// System automatically coordinates based on component readiness
		// No manual triggers needed

		// Complete startup
		fakeComponents["db"].EmitEvent(ComponentStarting)
		fakeComponents["fs"].EmitEvent(ComponentStarting)
		fakeComponents["db"].EmitEvent(ComponentStarted)
		fakeComponents["fs"].EmitEvent(ComponentStarted)
		fakeComponents["db"].EmitEvent(ComponentReady)
		fakeComponents["fs"].EmitEvent(ComponentReady)
		fakeProcess.EmitEvent(EventStarted)
		waitForSystemState(ssm, SystemStateRunning, 500*time.Millisecond)

		// Cause component failure to reach error state
		fakeComponents["db"].EmitEvent(ComponentFailed)
		waitForSystemState(ssm, SystemStateError, 500*time.Millisecond)

		// Now try to transition from error state - should be rejected
		err := ssm.Fire(SystemTriggerStart)
		if err == nil {
			t.Error("Error final state should reject transitions")
		}
	})
}

// Test reactive state changes (responding to component/process changes)
func TestSystemStateMachine_ReactiveStateChanges(t *testing.T) {
	t.Run("Process_Crash_Causes_Error", func(t *testing.T) {
		// Create test dependencies
		processSM, fakeProcess := NewTestableProcessStateMachine()
		componentSetSM, fakeComponents := NewTestableComponentSetStateMachine()

		// Clean up
		defer fakeProcess.Close()
		defer fakeComponents["db"].Close()
		defer fakeComponents["fs"].Close()

		// Create system state machine
		ssm := NewSystemState(componentSetSM, processSM)

		// Start and get to running state first

		// System automatically starts components, drive them through startup
		time.Sleep(10 * time.Millisecond) // Allow system to start components

		// Drive fake components through their startup sequence
		for _, fake := range fakeComponents {
			completeComponentStartup(fake)
		}

		// Complete process startup
		fakeProcess.EmitEvent(EventStarted)

		// Wait for system to reach Running state before crash test
		if !waitForSystemState(ssm, SystemStateRunning, 2000*time.Millisecond) {
			t.Fatalf("System should be Running before crash test, got %s", ssm.GetState())
		}

		// Simulate process crash - use EventFailed for permanent failure instead of EventExited (which restarts)
		fakeProcess.EmitEvent(EventFailed) // This should cause ProcessStateError

		// Wait for process to reach error state first
		time.Sleep(50 * time.Millisecond)

		// Verify process is in error state
		if ssm.GetProcessState() != ProcessStateError {
			t.Errorf("Expected process to be in Error state, got %s", ssm.GetProcessState())
		}

		// System should react and go to error state
		if !waitForSystemState(ssm, SystemStateError, 500*time.Millisecond) {
			t.Errorf("Expected Error after process crash, got %s", ssm.GetState())
		}

		// Verify error type
		if ssm.GetErrorType() != ErrorTypeProcessError {
			t.Errorf("Expected ProcessError error type, got %s", ssm.GetErrorType())
		}
	})

	t.Run("Component_Error_Causes_System_Error", func(t *testing.T) {
		// Create test dependencies
		processSM, fakeProcess := NewTestableProcessStateMachine()
		componentSetSM, fakeComponents := NewTestableComponentSetStateMachine()

		// Clean up
		defer fakeProcess.Close()
		defer fakeComponents["db"].Close()
		defer fakeComponents["fs"].Close()

		// Create system state machine
		ssm := NewSystemState(componentSetSM, processSM)

		// Start and get to running state first

		// System automatically starts components, drive them through startup
		time.Sleep(10 * time.Millisecond) // Allow system to start components

		// Drive fake components through their startup sequence
		for _, fake := range fakeComponents {
			completeComponentStartup(fake)
		}

		// Complete process startup
		fakeProcess.EmitEvent(EventStarted)

		// Wait for system to reach Running state before component error test
		if !waitForSystemState(ssm, SystemStateRunning, 2000*time.Millisecond) {
			t.Fatalf("System should be Running before component error test, got %s", ssm.GetState())
		}

		// Simulate component failure
		fakeComponents["db"].EmitEvent(ComponentFailed)

		// System should react and go to error state
		if !waitForSystemState(ssm, SystemStateError, 500*time.Millisecond) {
			t.Errorf("Expected Error after component failure, got %s", ssm.GetState())
		}

		// Verify error type
		if ssm.GetErrorType() != ErrorTypeDBError {
			t.Errorf("Expected DBError error type, got %s", ssm.GetErrorType())
		}
	})
}
