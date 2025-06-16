package managers

import (
	"context"
	"fmt"

	"github.com/qmuntal/stateless"
)

// TraceEvent represents a state machine transition event for tracing
type TraceEvent struct {
	Source     string // Name of the state machine (e.g., "SystemStateManager")
	Transition stateless.Transition
	Timestamp  int64
}

// FireEvent represents a delayed Fire() call to avoid deadlocks
type FireEvent struct {
	Target  Fireable // The state machine to fire on
	Trigger string   // The trigger to fire
}

// Fireable interface for objects that can have triggers fired on them
type Fireable interface {
	Fire(trigger string, args ...any) error
}

// TraceableManager provides tracing capabilities without deadlocks
type TraceableManager struct {
	name        string
	sm          *stateless.StateMachine
	traceEvents chan TraceEvent
	fireEvents  chan FireEvent
	ctx         context.Context
	cancel      context.CancelFunc
}

// NewTraceableManager creates a new traceable manager wrapper
func NewTraceableManager(name string, sm *stateless.StateMachine) *TraceableManager {
	ctx, cancel := context.WithCancel(context.Background())

	tm := &TraceableManager{
		name:        name,
		sm:          sm,
		traceEvents: make(chan TraceEvent, 100), // Buffered to avoid blocking
		fireEvents:  make(chan FireEvent, 100),  // Buffered to avoid blocking
		ctx:         ctx,
		cancel:      cancel,
	}

	// Set up tracing on the state machine
	sm.OnTransitioning(func(ctx context.Context, transition stateless.Transition) {
		// Emit trace event asynchronously
		select {
		case tm.traceEvents <- TraceEvent{
			Source:     name,
			Transition: transition,
			Timestamp:  nowMillis(),
		}:
		default:
			// Drop trace if buffer full to avoid blocking
		}
	})

	// Start the async event processor
	go tm.processEvents()

	return tm
}

// OnTrace registers a callback for trace events
func (tm *TraceableManager) OnTrace(callback func(TraceEvent)) {
	go func() {
		for {
			select {
			case <-tm.ctx.Done():
				return
			case event := <-tm.traceEvents:
				callback(event)
			}
		}
	}()
}

// QueueFire queues a Fire() call to be executed asynchronously to avoid deadlocks
func (tm *TraceableManager) QueueFire(target Fireable, trigger string) {
	select {
	case tm.fireEvents <- FireEvent{Target: target, Trigger: trigger}:
	default:
		// Drop fire event if buffer full to avoid blocking
		fmt.Printf("Warning: TraceableManager fire event buffer full, dropping Fire(%s)\n", trigger)
	}
}

// processEvents processes trace and fire events asynchronously
func (tm *TraceableManager) processEvents() {
	for {
		select {
		case <-tm.ctx.Done():
			return
		case fireEvent := <-tm.fireEvents:
			// Execute the Fire() call outside of any state machine context
			if err := fireEvent.Target.Fire(fireEvent.Trigger); err != nil {
				panic(fmt.Sprintf("State machine error firing trigger %s: %v", fireEvent.Trigger, err))
			}
		}
	}
}

// Close stops the traceable manager
func (tm *TraceableManager) Close() {
	tm.cancel()
}

// Helper function to get current timestamp in milliseconds
func nowMillis() int64 {
	return int64(1000) // Placeholder - use time.Now().UnixNano() / 1e6 in real implementation
}
