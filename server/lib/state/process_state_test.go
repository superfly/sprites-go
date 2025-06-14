package state

import (
	"context"
	"os"
	"sprite-env/lib/adapters"
	"syscall"
	"testing"
	"time"

	"github.com/qmuntal/stateless"
)

// FakeProcess implements ProcessInterface for testing
type FakeProcess struct {
	closed   bool
	ctx      context.Context
	cancel   context.CancelFunc
	handlers adapters.ProcessEventHandlers
}

// TrackingFakeProcess implements ProcessInterface and tracks when methods are called
type TrackingFakeProcess struct {
	closed      bool
	startCalled bool
	stopCalled  bool
	signalCalls []os.Signal
	handlers    adapters.ProcessEventHandlers
	ctx         context.Context
	cancel      context.CancelFunc
}

// NewTrackingFakeProcess creates a new tracking fake process for testing
func NewTrackingFakeProcess() *TrackingFakeProcess {
	ctx, cancel := context.WithCancel(context.Background())
	return &TrackingFakeProcess{
		signalCalls: make([]os.Signal, 0),
		ctx:         ctx,
		cancel:      cancel,
	}
}

// Start implements ProcessInterface and tracks that it was called
func (f *TrackingFakeProcess) Start(ctx context.Context) error {
	f.startCalled = true
	return nil
}

// Stop implements ProcessInterface and tracks that it was called
func (f *TrackingFakeProcess) Stop() {
	f.stopCalled = true
}

// Signal implements ProcessInterface and tracks signals
func (f *TrackingFakeProcess) Signal(sig os.Signal) {
	f.signalCalls = append(f.signalCalls, sig)
}

// SetEventHandlers implements ProcessInterface
func (f *TrackingFakeProcess) SetEventHandlers(handlers adapters.ProcessEventHandlers) {
	f.handlers = handlers
}

// EmitEvent sends an event for testing (not part of ProcessInterface)
func (f *TrackingFakeProcess) EmitEvent(event adapters.EventType) {
	// Call the handlers if set (Observer pattern)
	// Use context to avoid goroutine leaks in tests
	if f.ctx != nil {
		go func() {
			// Check if context is canceled before running handler
			select {
			case <-f.ctx.Done():
				return // Context canceled, don't run handler
			default:
			}

			switch event {
			case adapters.EventStarting:
				if f.handlers.Starting != nil {
					f.handlers.Starting()
				}
			case adapters.EventStarted:
				if f.handlers.Started != nil {
					f.handlers.Started()
				}
			case adapters.EventStopping:
				if f.handlers.Stopping != nil {
					f.handlers.Stopping()
				}
			case adapters.EventStopped:
				if f.handlers.Stopped != nil {
					f.handlers.Stopped()
				}
			case adapters.EventSignaled:
				if f.handlers.Signaled != nil {
					f.handlers.Signaled(syscall.SIGKILL) // Default to SIGKILL for testing
				}
			case adapters.EventExited:
				if f.handlers.Exited != nil {
					f.handlers.Exited()
				}
			case adapters.EventRestarting:
				if f.handlers.Restarting != nil {
					f.handlers.Restarting()
				}
			case adapters.EventFailed:
				if f.handlers.Failed != nil {
					f.handlers.Failed(nil)
				}
			}
		}()
	}
}

// Close cleans up the fake process
func (f *TrackingFakeProcess) Close() {
	if !f.closed {
		f.closed = true
		// Cancel context to clean up any running handler goroutines
		if f.cancel != nil {
			f.cancel()
		}
	}
}

// WasStartCalled returns whether Start() was called
func (f *TrackingFakeProcess) WasStartCalled() bool {
	return f.startCalled
}

// WasStopCalled returns whether Stop() was called
func (f *TrackingFakeProcess) WasStopCalled() bool {
	return f.stopCalled
}

// GetSignalCalls returns all signals that were sent
func (f *TrackingFakeProcess) GetSignalCalls() []os.Signal {
	return f.signalCalls
}

// NewFakeProcess creates a new fake process for testing
func NewFakeProcess() *FakeProcess {
	ctx, cancel := context.WithCancel(context.Background())
	return &FakeProcess{
		ctx:    ctx,
		cancel: cancel,
	}
}

// Start implements ProcessInterface - returns error instead of channel
func (f *FakeProcess) Start(ctx context.Context) error {
	return nil
}

// Stop implements ProcessInterface - no-op for testing
func (f *FakeProcess) Stop() {
	// No-op for testing
}

// Signal implements ProcessInterface - no-op for testing
func (f *FakeProcess) Signal(sig os.Signal) {
	// No-op for testing
}

// SetEventHandlers implements ProcessInterface
func (f *FakeProcess) SetEventHandlers(handlers adapters.ProcessEventHandlers) {
	f.handlers = handlers
}

// EmitEvent sends an event for testing (not part of ProcessInterface)
func (f *FakeProcess) EmitEvent(event adapters.EventType) {
	// Call the handlers if set (Observer pattern)
	// Use context to avoid goroutine leaks in tests
	if f.ctx != nil {
		go func() {
			// Check if context is canceled before running handler
			select {
			case <-f.ctx.Done():
				return // Context canceled, don't run handler
			default:
			}

			switch event {
			case adapters.EventStarting:
				if f.handlers.Starting != nil {
					f.handlers.Starting()
				}
			case adapters.EventStarted:
				if f.handlers.Started != nil {
					f.handlers.Started()
				}
			case adapters.EventStopping:
				if f.handlers.Stopping != nil {
					f.handlers.Stopping()
				}
			case adapters.EventStopped:
				if f.handlers.Stopped != nil {
					f.handlers.Stopped()
				}
			case adapters.EventSignaled:
				if f.handlers.Signaled != nil {
					f.handlers.Signaled(syscall.SIGKILL) // Default to SIGKILL for testing
				}
			case adapters.EventExited:
				if f.handlers.Exited != nil {
					f.handlers.Exited()
				}
			case adapters.EventRestarting:
				if f.handlers.Restarting != nil {
					f.handlers.Restarting()
				}
			case adapters.EventFailed:
				if f.handlers.Failed != nil {
					f.handlers.Failed(nil)
				}
			}
		}()
	}
}

// Close cleans up the fake process
func (f *FakeProcess) Close() {
	if !f.closed {
		f.closed = true
		// Cancel context to clean up any running handler goroutines
		if f.cancel != nil {
			f.cancel()
		}
	}
}

// waitForState waits for the state machine to reach the expected state
func waitForState(psm *ProcessState, expected ProcessStateType, timeout time.Duration) bool {
	deadline := time.Now().Add(timeout)
	for time.Now().Before(deadline) {
		if psm.MustState() == expected {
			return true
		}
		time.Sleep(time.Millisecond)
	}
	return false
}

// Test complete process lifecycle event sequences
func TestProcessStateMachine_TLASpecSequences(t *testing.T) {
	t.Run("Complete_Startup_Sequence", func(t *testing.T) {
		fake := NewFakeProcess()
		defer fake.Close()

		psm := NewProcessStateWithProcess(fake)
		ctx := context.Background()

		// Start the process from Initializing state
		if err := psm.Fire(TriggerStart, ctx); err != nil {
			t.Fatalf("Failed to start process: %v", err)
		}

		// Complete startup event sequence: Starting → Running
		fake.EmitEvent(adapters.EventStarting) // Optional: process beginning startup
		fake.EmitEvent(adapters.EventStarted)  // Process fully started

		if !waitForState(psm, ProcessStateRunning, 10*time.Second) {
			t.Errorf("Expected Running after startup sequence, got %s", psm.MustState())
		}
	})

	t.Run("Complete_Stop_Sequence", func(t *testing.T) {
		fake := NewFakeProcess()
		defer fake.Close()

		psm := NewProcessStateWithProcess(fake)
		ctx := context.Background()

		// Complete startup sequence: Initializing → Starting → Running
		if err := psm.Fire(TriggerStart, ctx); err != nil {
			t.Fatalf("Failed to start process: %v", err)
		}
		fake.EmitEvent(adapters.EventStarting) // Process beginning startup
		fake.EmitEvent(adapters.EventStarted)  // Process fully started
		waitForState(psm, ProcessStateRunning, 10*time.Second)

		// Complete stop sequence: Running → Stopping → Stopped
		if err := psm.Fire(TriggerStop); err != nil {
			t.Fatalf("Failed to stop process: %v", err)
		}
		fake.EmitEvent(adapters.EventStopping) // Process beginning shutdown
		fake.EmitEvent(adapters.EventStopped)  // Process fully stopped

		if !waitForState(psm, ProcessStateStopped, 10*time.Second) {
			t.Errorf("Expected Stopped after stop sequence, got %s", psm.MustState())
		}
	})

	t.Run("Complete_Crash_Restart_Sequence", func(t *testing.T) {
		fake := NewFakeProcess()
		defer fake.Close()

		psm := NewProcessStateWithProcess(fake)
		ctx := context.Background()

		// Complete startup: Initializing → Starting → Running
		psm.Fire(TriggerStart, ctx)
		fake.EmitEvent(adapters.EventStarting)
		fake.EmitEvent(adapters.EventStarted)
		waitForState(psm, ProcessStateRunning, 10*time.Second)

		// Crash: Running → Crashed
		fake.EmitEvent(adapters.EventExited)
		waitForState(psm, ProcessStateCrashed, 10*time.Second)

		// Complete restart: Crashed → Starting → Running
		if err := psm.Fire(TriggerRestart, ctx); err != nil {
			t.Fatalf("Failed to restart process: %v", err)
		}

		// Process events after restart trigger - no EventRestarting needed since we fired TriggerRestart directly
		fake.EmitEvent(adapters.EventStarting) // Process beginning startup again
		fake.EmitEvent(adapters.EventStarted)  // Process fully running again

		if !waitForState(psm, ProcessStateRunning, 10*time.Second) {
			t.Errorf("Expected Running after restart sequence, got %s", psm.MustState())
		}
	})

	t.Run("Kill_Sequence", func(t *testing.T) {
		fake := NewFakeProcess()
		defer fake.Close()

		psm := NewProcessStateWithProcess(fake)
		ctx := context.Background()

		// Complete startup sequence: Initializing → Starting → Running
		if err := psm.Fire(TriggerStart, ctx); err != nil {
			t.Fatalf("Failed to start process: %v", err)
		}
		fake.EmitEvent(adapters.EventStarting) // Process beginning startup
		fake.EmitEvent(adapters.EventStarted)  // Process fully started
		waitForState(psm, ProcessStateRunning, 10*time.Second)

		// Complete kill sequence: Running → Signaling → Killed
		if err := psm.Fire(TriggerSignal); err != nil {
			t.Fatalf("Failed to signal process: %v", err)
		}
		// Process gets SIGKILL and dies
		psm.lastSignal = syscall.SIGKILL       // Set the signal type for proper mapping
		fake.EmitEvent(adapters.EventSignaled) // Process received SIGKILL and died

		if !waitForState(psm, ProcessStateKilled, 10*time.Second) {
			t.Errorf("Expected Killed after signal sequence, got %s", psm.MustState())
		}
	})
}

// Test that process events map to correct state transitions
func TestProcessStateMachine_EventMapping(t *testing.T) {
	tests := []struct {
		startState ProcessStateType
		event      adapters.EventType
		expectEnd  ProcessStateType
	}{
		{ProcessStateStarting, adapters.EventStarted, ProcessStateRunning},
		{ProcessStateRunning, adapters.EventExited, ProcessStateCrashed},
		{ProcessStateRunning, adapters.EventFailed, ProcessStateError},
		{ProcessStateStopping, adapters.EventStopped, ProcessStateStopped},
	}

	for _, tt := range tests {
		t.Run(string(tt.event), func(t *testing.T) {
			fake := NewFakeProcess()
			defer fake.Close()

			// Create state machine in start state
			psm := &ProcessState{process: fake}
			psm.StateMachine = stateless.NewStateMachine(tt.startState)
			psm.configureStateMachine()

			// Set up event handlers for the Observer pattern
			psm.setupEventHandlers()

			// Special case for SIGKILL mapping
			if tt.event == adapters.EventSignaled {
				psm.lastSignal = syscall.SIGKILL
			}

			// Emit the event through the fake process (this will trigger handlers)
			fake.EmitEvent(tt.event)

			// Give the event handler time to run (it runs in a goroutine)
			time.Sleep(10 * time.Millisecond)

			if psm.MustState().(ProcessStateType) != tt.expectEnd {
				t.Errorf("Expected %s, got %s", tt.expectEnd, psm.MustState())
			}
		})
	}
}

// Test that final states reject further transitions
func TestProcessStateMachine_FinalStates(t *testing.T) {
	finalStates := []ProcessStateType{ProcessStateStopped, ProcessStateShutdown, ProcessStateKilled, ProcessStateError}

	for _, state := range finalStates {
		t.Run(string(state), func(t *testing.T) {
			fake := NewFakeProcess()
			defer fake.Close()

			psm := &ProcessState{process: fake}
			psm.StateMachine = stateless.NewStateMachine(state)
			psm.configureStateMachine()

			err := psm.Fire(TriggerStart, context.Background())
			if err == nil {
				t.Error("Final state should reject transitions")
			}
		})
	}
}

// Test that process.Start() is only called when transitioning to Running state, not during initialization
func TestProcessStateMachine_StartCalledAtRightTime(t *testing.T) {
	t.Run("Start_Not_Called_During_Initialization", func(t *testing.T) {
		fake := NewTrackingFakeProcess()
		defer fake.Close()

		// Create the state machine - this should NOT call Start()
		psm := NewProcessStateWithProcess(fake)

		// Verify Start was NOT called during initialization
		if fake.WasStartCalled() {
			t.Error("process.Start() was called during initialization, but should only be called when firing TriggerStart")
		}

		// Verify we're in Initializing state
		if psm.MustState() != ProcessStateInitializing {
			t.Errorf("Expected Initializing state after creation, got %s", psm.MustState())
		}
	})

	t.Run("Start_Called_When_Requesting_Running_State", func(t *testing.T) {
		fake := NewTrackingFakeProcess()
		defer fake.Close()

		// Create the state machine
		psm := NewProcessStateWithProcess(fake)
		ctx := context.Background()

		// Verify Start was NOT called yet
		if fake.WasStartCalled() {
			t.Error("process.Start() was called during initialization")
		}

		// Start the process - this SHOULD call Start()
		if err := psm.Fire(TriggerStart, ctx); err != nil {
			t.Fatalf("Failed to start process: %v", err)
		}

		// Verify Start was called when we fired TriggerStart
		if !fake.WasStartCalled() {
			t.Error("process.Start() was NOT called when firing TriggerStart, but it should have been")
		}
	})
}

// NewTestableProcessStateMachine creates a testable process state machine for system state testing
func NewTestableProcessStateMachine() (*ProcessState, *FakeProcess) {
	fake := NewFakeProcess()
	psm := NewProcessStateWithProcess(fake)
	return psm, fake
}
