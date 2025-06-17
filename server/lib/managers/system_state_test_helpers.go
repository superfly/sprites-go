package managers

import (
	"context"
	"fmt"
	"os"
	"sprite-env/lib"
	"sprite-env/lib/adapters"
	"testing"
	"time"
)

// TestScenario represents a comprehensive test scenario for system state management
type TestScenario struct {
	Name               string
	Description        string
	Setup              func(*EnhancedStateManagerRefs) error
	Sequence           []string
	ExpectedFinalState string
	ExpectedCalls      map[string]int
	ExpectedEvents     []string
	ShouldFail         bool
	FailurePoint       string
	Invariants         []func(*EnhancedStateManagerRefs) bool
}

// CallTracker tracks method calls on mock objects
type CallTracker struct {
	ProcessStartCalls   int
	ProcessStopCalls    int
	ProcessSignalCalls  int
	ComponentStartCalls int
	ComponentStopCalls  int
	LastSignal          os.Signal
}

// EnhancedTestManagedProcess provides comprehensive call tracking for testing
type EnhancedTestManagedProcess struct {
	name                string
	startCalls          int
	stopCalls           int
	signalCalls         int
	lastSignal          os.Signal
	eventsCh            chan adapters.ProcessEventType
	shouldFailStart     bool
	shouldSucceedStart  bool
	autoTransitionDelay time.Duration
}

func NewEnhancedTestManagedProcess(shouldSucceedStart bool) *EnhancedTestManagedProcess {
	return &EnhancedTestManagedProcess{
		name:                "enhanced-test-process",
		eventsCh:            make(chan adapters.ProcessEventType, 10),
		shouldSucceedStart:  shouldSucceedStart,
		autoTransitionDelay: 1 * time.Millisecond,
	}
}

func (tmp *EnhancedTestManagedProcess) Start(ctx context.Context) error {
	tmp.startCalls++
	if tmp.shouldFailStart {
		// Send Error event after a brief delay
		go func() {
			time.Sleep(tmp.autoTransitionDelay)
			select {
			case tmp.eventsCh <- adapters.ProcessFailedEvent:
			default:
			}
		}()
		return fmt.Errorf("simulated start failure")
	}
	if tmp.shouldSucceedStart {
		// Send Started event after a brief delay
		go func() {
			time.Sleep(tmp.autoTransitionDelay)
			select {
			case tmp.eventsCh <- adapters.ProcessStartedEvent:
			default:
			}
		}()
	}
	return nil
}

func (tmp *EnhancedTestManagedProcess) Stop() {
	tmp.stopCalls++
	// Send Stopped event after a brief delay
	go func() {
		time.Sleep(tmp.autoTransitionDelay)
		select {
		case tmp.eventsCh <- adapters.ProcessStoppedEvent:
		default:
		}
	}()
}

func (tmp *EnhancedTestManagedProcess) Signal(sig os.Signal) {
	tmp.signalCalls++
	tmp.lastSignal = sig
}

func (tmp *EnhancedTestManagedProcess) Events() <-chan adapters.ProcessEventType {
	return tmp.eventsCh
}

func (tmp *EnhancedTestManagedProcess) GetCallTracker() CallTracker {
	return CallTracker{
		ProcessStartCalls:  tmp.startCalls,
		ProcessStopCalls:   tmp.stopCalls,
		ProcessSignalCalls: tmp.signalCalls,
		LastSignal:         tmp.lastSignal,
	}
}

func (tmp *EnhancedTestManagedProcess) TriggerEvent(event adapters.ProcessEventType) {
	select {
	case tmp.eventsCh <- event:
	default:
	}
}

// EnhancedTestManagedComponent provides comprehensive call tracking for testing
type EnhancedTestManagedComponent struct {
	name                 string
	startCalls           int
	stopCalls            int
	checkpointCalls      int
	restoreCalls         int
	eventsCh             chan adapters.ComponentEventType
	shouldFailStart      bool
	autoTransitionDelay  time.Duration
	checkpointCalled     bool
	log                  []string
	shouldFailCheckpoint bool
	shouldFailRestore    bool
}

func NewEnhancedTestManagedComponent(name string, shouldFailStart bool) *EnhancedTestManagedComponent {
	return &EnhancedTestManagedComponent{
		name:                name,
		eventsCh:            make(chan adapters.ComponentEventType, 10),
		shouldFailStart:     shouldFailStart,
		autoTransitionDelay: 1 * time.Millisecond,
	}
}

func (mc *EnhancedTestManagedComponent) GetName() string {
	return mc.name
}

func (mc *EnhancedTestManagedComponent) Start(ctx context.Context) error {
	mc.startCalls++
	if mc.shouldFailStart {
		go func() {
			time.Sleep(mc.autoTransitionDelay)
			select {
			case mc.eventsCh <- adapters.ComponentFailed:
			default:
			}
		}()
		return fmt.Errorf("simulated component start failure")
	}
	// Send Started event after a brief delay
	go func() {
		time.Sleep(mc.autoTransitionDelay)
		select {
		case mc.eventsCh <- adapters.ComponentStarted:
		default:
		}
	}()
	return nil
}

func (mc *EnhancedTestManagedComponent) Stop() {
	mc.stopCalls++
	// Send Stopped event after a brief delay
	go func() {
		time.Sleep(mc.autoTransitionDelay)
		select {
		case mc.eventsCh <- adapters.ComponentStopped:
		default:
		}
	}()
}

func (mc *EnhancedTestManagedComponent) Checkpoint(checkpointID string) error {
	mc.checkpointCalled = true
	mc.checkpointCalls++
	if checkpointID != "" {
		mc.log = append(mc.log, "checkpoint with ID: "+checkpointID)
	} else {
		mc.log = append(mc.log, "checkpoint")
	}
	if mc.shouldFailCheckpoint {
		return fmt.Errorf("checkpoint failed")
	}
	// Send checkpoint complete event
	go func() {
		time.Sleep(mc.autoTransitionDelay)
		mc.TriggerEvent(adapters.ComponentCheckpointed)
	}()
	return nil
}

func (mc *EnhancedTestManagedComponent) Restore(checkpointID string) error {
	mc.restoreCalls++
	if checkpointID != "" {
		mc.log = append(mc.log, "restore with ID: "+checkpointID)
	} else {
		mc.log = append(mc.log, "restore")
	}
	if mc.shouldFailRestore {
		return fmt.Errorf("restore failed")
	}
	// Send restore complete event
	go func() {
		time.Sleep(mc.autoTransitionDelay)
		mc.TriggerEvent(adapters.ComponentRestored)
	}()
	return nil
}

func (mc *EnhancedTestManagedComponent) Events() <-chan adapters.ComponentEventType {
	return mc.eventsCh
}

func (mc *EnhancedTestManagedComponent) GetCallTracker() CallTracker {
	return CallTracker{
		ComponentStartCalls: mc.startCalls,
		ComponentStopCalls:  mc.stopCalls,
	}
}

func (mc *EnhancedTestManagedComponent) TriggerEvent(event adapters.ComponentEventType) {
	select {
	case mc.eventsCh <- event:
	default:
	}
}

// EnhancedStateManagerRefs holds references to all state managers with call tracking
type EnhancedStateManagerRefs struct {
	System         *SystemState
	Process        *ProcessState
	ComponentGroup *ComponentGroupState
	Components     []*ComponentState
	TestProcess    *EnhancedTestManagedProcess
	TestComponents []*EnhancedTestManagedComponent
	StateChanges   *[]string
}

func (refs *EnhancedStateManagerRefs) GetAggregatedCallTracker() CallTracker {
	tracker := CallTracker{}

	if refs.TestProcess != nil {
		processTracker := refs.TestProcess.GetCallTracker()
		tracker.ProcessStartCalls = processTracker.ProcessStartCalls
		tracker.ProcessStopCalls = processTracker.ProcessStopCalls
		tracker.ProcessSignalCalls = processTracker.ProcessSignalCalls
		tracker.LastSignal = processTracker.LastSignal
	}

	for _, comp := range refs.TestComponents {
		compTracker := comp.GetCallTracker()
		tracker.ComponentStartCalls += compTracker.ComponentStartCalls
		tracker.ComponentStopCalls += compTracker.ComponentStopCalls
	}

	return tracker
}

func (refs *EnhancedStateManagerRefs) Close() {
	if refs.System != nil {
		refs.System.Close()
	}
	if refs.Process != nil {
		refs.Process.Close()
	}
}

// WaitForTerminalState waits for the system to reach a terminal state (Error or Stopped)
// Returns the final state or times out after the specified duration
func (refs *EnhancedStateManagerRefs) WaitForTerminalState(timeout time.Duration) string {
	start := time.Now()
	for {
		currentState := refs.System.MustState().(string)
		if currentState == "Error" || currentState == "Stopped" {
			return currentState
		}

		// Check for timeout
		if time.Since(start) > timeout {
			return currentState // Return current state even if not terminal
		}

		// Small sleep to avoid busy waiting
		time.Sleep(1 * time.Millisecond)
	}
}

// WaitForStateStability waits for the state changes to stop for a specified duration
// indicating the system has reached stability
func (refs *EnhancedStateManagerRefs) WaitForStateStability(stabilityDuration time.Duration, maxWait time.Duration) string {
	lastChangeCount := len(*refs.StateChanges)
	lastChangeTime := time.Now()
	start := time.Now()

	for {
		currentChangeCount := len(*refs.StateChanges)
		now := time.Now()

		// If we have new state changes, reset the stability timer
		if currentChangeCount > lastChangeCount {
			lastChangeCount = currentChangeCount
			lastChangeTime = now
		}

		// If we've been stable for the required duration, we're done
		if now.Sub(lastChangeTime) >= stabilityDuration {
			return refs.System.MustState().(string)
		}

		// Check for overall timeout
		if now.Sub(start) > maxWait {
			return refs.System.MustState().(string)
		}

		// Small sleep to avoid busy waiting
		time.Sleep(1 * time.Millisecond)
	}
}

// CreateEnhancedSystemWithAllManagers creates a system with comprehensive tracking for testing
func CreateEnhancedSystemWithAllManagers(t *testing.T, numComponents int, processSucceeds bool, componentFailures []bool) (*EnhancedStateManagerRefs, *[]string) {
	return CreateEnhancedSystemWithAllManagersAndConfig(t, numComponents, processSucceeds, componentFailures, nil)
}

// CreateEnhancedSystemWithAllManagersAndConfig creates a system with comprehensive tracking and optional config for testing
func CreateEnhancedSystemWithAllManagersAndConfig(t *testing.T, numComponents int, processSucceeds bool, componentFailures []bool, systemConfig *SystemConfig) (*EnhancedStateManagerRefs, *[]string) {
	// Create enhanced mock components
	var components []ManagedComponent
	var testComponents []*EnhancedTestManagedComponent

	for i := 0; i < numComponents; i++ {
		shouldFail := false
		if i < len(componentFailures) {
			shouldFail = componentFailures[i]
		}
		comp := NewEnhancedTestManagedComponent(fmt.Sprintf("component-%d", i), shouldFail)
		components = append(components, comp)
		testComponents = append(testComponents, comp)
	}

	// Create enhanced mock process (without auto events for precise test control)
	testProcess := NewEnhancedTestManagedProcess(processSucceeds)
	psm := NewProcessState(ProcessStateConfig{
		Process: testProcess,
	}, []lib.StateMonitor(nil))

	// Create state change recorder
	var stateChanges []string
	systemMonitor := NewTestStateMonitor("SystemState", &stateChanges)

	// Create system config
	config := SystemConfig{
		ProcessState: psm,
		Components:   components,
	}

	// Override with provided config if given
	if systemConfig != nil {
		if systemConfig.InitialState != "" {
			config.InitialState = systemConfig.InitialState
		}
		if systemConfig.ProcessState != nil {
			config.ProcessState = systemConfig.ProcessState
		}
		if systemConfig.Components != nil {
			config.Components = systemConfig.Components
		}
	}

	// Create system state manager
	ssm := NewSystemState(config, []lib.StateMonitor{systemMonitor})

	// Get references to all state managers
	refs := &EnhancedStateManagerRefs{
		System:         ssm,
		Process:        psm,
		TestProcess:    testProcess,
		TestComponents: testComponents,
		StateChanges:   &stateChanges,
	}

	// Get component group reference (if components exist)
	if len(components) > 0 {
		refs.ComponentGroup = ssm.componentGroupState
		if refs.ComponentGroup != nil {
			refs.Components = refs.ComponentGroup.GetComponentStates()
		}
	}

	return refs, &stateChanges
}

// TestStateMonitor implements StateMonitor for testing
type TestStateMonitor struct {
	name         string
	stateChanges *[]string
	events       chan lib.StateTransition
	done         chan struct{}
	finished     chan struct{}
}

func NewTestStateMonitor(name string, stateChanges *[]string) *TestStateMonitor {
	monitor := &TestStateMonitor{
		name:         name,
		stateChanges: stateChanges,
		events:       make(chan lib.StateTransition, 50), // Buffered channel
		done:         make(chan struct{}),
		finished:     make(chan struct{}),
	}

	// Start a goroutine to process events
	go monitor.processEvents()

	return monitor
}

// Events implements StateMonitor interface
func (tsm *TestStateMonitor) Events() chan<- lib.StateTransition {
	return tsm.events
}

// Close implements io.Closer interface for graceful shutdown
func (tsm *TestStateMonitor) Close() error {
	// Signal shutdown
	close(tsm.done)

	// Wait for processing to finish with a reasonable timeout
	timeout := 1 * time.Second
	select {
	case <-tsm.finished:
		// Graceful shutdown completed
		return nil
	case <-time.After(timeout):
		// Timeout - force close
		return fmt.Errorf("testStateMonitor close timeout after %v", timeout)
	}
}

// processEvents processes state transition events for testing
func (tsm *TestStateMonitor) processEvents() {
	defer close(tsm.finished)

	for {
		select {
		case <-tsm.done:
			// Drain remaining events before shutdown
			for {
				select {
				case transition := <-tsm.events:
					if transition.Name == tsm.name {
						*tsm.stateChanges = append(*tsm.stateChanges, transition.To)
					}
				default:
					// No more events, shutdown complete
					return
				}
			}
		case transition := <-tsm.events:
			if transition.Name == tsm.name {
				*tsm.stateChanges = append(*tsm.stateChanges, transition.To)
			}
		}
	}
}
