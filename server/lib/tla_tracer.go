package lib

import (
	"encoding/json"
	"fmt"
	"log/slog"
	"os"
	"sync"
)

// TLAStateSimple represents the core state variables for TLA+ specification compliance
type TLAStateSimple struct {
	SystemState       string `json:"systemState"` // Updated from overallState to match new spec
	ComponentSetState string `json:"componentSetState"`
	DbState           string `json:"dbState"`
	FsState           string `json:"fsState"`
	ProcessState      string `json:"processState"`
}

// TLATracer manages TLA+ specification compliant trace emission
type TLATracer struct {
	enabled bool
	debug   bool
	mu      sync.RWMutex
	state   TLAStateSimple
}

// NewTLATracer creates a new TLA tracer
func NewTLATracer(enabled bool, debug bool) *TLATracer {
	return &TLATracer{
		enabled: enabled,
		debug:   debug,
		state: TLAStateSimple{
			SystemState:       "Initializing",
			ComponentSetState: "Initializing",
			DbState:           "Initializing",
			FsState:           "Initializing",
			ProcessState:      "Initializing",
		},
	}
}

// UpdateOverallState updates the system state and emits trace if enabled
// Kept old method name for backward compatibility
func (t *TLATracer) UpdateOverallState(state string) {
	t.mu.Lock()
	defer t.mu.Unlock()

	if t.state.SystemState != state {
		t.state.SystemState = state
		t.emitTrace("systemState", state)
	}
}

// UpdateSystemState updates the system state and emits trace if enabled
func (t *TLATracer) UpdateSystemState(state string) {
	t.UpdateOverallState(state) // Delegate to existing method for compatibility
}

// UpdateComponentSetState updates the component set state and emits trace if enabled
func (t *TLATracer) UpdateComponentSetState(state string) {
	t.mu.Lock()
	defer t.mu.Unlock()

	if t.state.ComponentSetState != state {
		t.state.ComponentSetState = state
		t.emitTrace("componentSetState", state)
	}
}

// UpdateDBState updates the DB state and emits trace if enabled
func (t *TLATracer) UpdateDBState(state string) {
	t.mu.Lock()
	defer t.mu.Unlock()

	if t.state.DbState != state {
		t.state.DbState = state
		t.emitTrace("dbState", state)
	}
}

// UpdateFSState updates the FS state and emits trace if enabled
func (t *TLATracer) UpdateFSState(state string) {
	t.mu.Lock()
	defer t.mu.Unlock()

	if t.state.FsState != state {
		t.state.FsState = state
		t.emitTrace("fsState", state)
	}
}

// UpdateProcessState updates the process state and emits trace if enabled
func (t *TLATracer) UpdateProcessState(state string) {
	t.mu.Lock()
	defer t.mu.Unlock()

	if t.state.ProcessState != state {
		t.state.ProcessState = state
		t.emitTrace("processState", state)
	}
}

// GetCurrentState returns a copy of the current state
func (t *TLATracer) GetCurrentState() TLAStateSimple {
	t.mu.RLock()
	defer t.mu.RUnlock()
	return t.state
}

// emitTrace writes the state change to stderr as JSON (called with lock held)
func (t *TLATracer) emitTrace(variable string, value string) {
	if !t.enabled {
		return
	}

	trace := map[string]interface{}{
		"variable": variable,
		"value":    value,
		"state":    t.state,
	}

	jsonBytes, err := json.Marshal(trace)
	if err != nil {
		if t.debug {
			slog.Error("Failed to marshal TLA trace", "error", err)
		}
		return
	}

	// Write to stderr for test runner to capture
	fmt.Fprintf(os.Stderr, "%s\n", jsonBytes)
}

// Enable enables or disables trace emission
func (t *TLATracer) Enable(enabled bool) {
	t.mu.Lock()
	defer t.mu.Unlock()
	t.enabled = enabled
}

// IsEnabled returns true if tracing is enabled
func (t *TLATracer) IsEnabled() bool {
	t.mu.RLock()
	defer t.mu.RUnlock()
	return t.enabled
}
