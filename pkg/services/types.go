package services

import (
	"context"
	"fmt"
	"io"
	"sync"
	"time"
)

// Service represents a service definition
type Service struct {
	Name  string   `json:"name"`
	Cmd   string   `json:"cmd"`
	Args  []string `json:"args"`
	Needs []string `json:"needs"` // Dependencies on other services
}

// ServiceState represents the runtime state of a service
type ServiceState struct {
	Name      string    `json:"name"`
	Status    Status    `json:"status"`
	PID       int       `json:"pid,omitempty"`
	StartedAt time.Time `json:"started_at,omitempty"`
	Error     string    `json:"error,omitempty"`
}

// Status represents the state of a service
type Status string

const (
	StatusStopped  Status = "stopped"
	StatusStarting Status = "starting"
	StatusRunning  Status = "running"
	StatusStopping Status = "stopping"
	StatusFailed   Status = "failed"
)

// StartResult represents the result of starting and monitoring a service
type StartResult struct {
	Started   bool  // Whether the service started successfully
	Completed bool  // Whether the service completed (exited) within the monitoring duration
	ExitCode  int   // Exit code if the service completed
	Error     error // Error if start failed or other error occurred
}

// ProcessHandle represents a running process
type ProcessHandle struct {
	PID          int
	Cancel       context.CancelFunc
	Done         <-chan struct{} // Closed when process exits
	ExitCode     <-chan int      // Receives exit code when process exits
	exitCodeVal  int             // Stored exit code value
	exitCodeSet  bool            // Whether exit code has been set
	stdoutLogger io.Writer       // Stdout logger that can have writers attached/removed
	stderrLogger io.Writer       // Stderr logger that can have writers attached/removed
	mu           sync.Mutex      // Protects exitCodeVal and exitCodeSet
}

// AttachStdout attaches a writer to receive stdout output
func (h *ProcessHandle) AttachStdout(w io.Writer) {
	if logger, ok := h.stdoutLogger.(*LineLogger); ok {
		logger.AttachWriter(w)
	}
}

// RemoveStdout removes a writer from receiving stdout output
func (h *ProcessHandle) RemoveStdout(w io.Writer) {
	if logger, ok := h.stdoutLogger.(*LineLogger); ok {
		logger.RemoveWriter(w)
	}
}

// AttachStderr attaches a writer to receive stderr output
func (h *ProcessHandle) AttachStderr(w io.Writer) {
	if logger, ok := h.stderrLogger.(*LineLogger); ok {
		logger.AttachWriter(w)
	}
}

// RemoveStderr removes a writer from receiving stderr output
func (h *ProcessHandle) RemoveStderr(w io.Writer) {
	if logger, ok := h.stderrLogger.(*LineLogger); ok {
		logger.RemoveWriter(w)
	}
}

// SetExitCode stores the exit code for later retrieval
func (h *ProcessHandle) SetExitCode(code int) {
	h.mu.Lock()
	defer h.mu.Unlock()
	h.exitCodeVal = code
	h.exitCodeSet = true
}

// Wait waits for the process to exit and returns the exit code.
// Returns an error if the timeout is reached before the process exits.
func (h *ProcessHandle) Wait(timeout time.Duration) (int, error) {
	select {
	case <-h.Done:
		// Process has exited, check if we have a stored exit code
		h.mu.Lock()
		if h.exitCodeSet {
			code := h.exitCodeVal
			h.mu.Unlock()
			return code, nil
		}
		h.mu.Unlock()

		// Try to get exit code from channel
		select {
		case code := <-h.ExitCode:
			h.SetExitCode(code)
			return code, nil
		case <-time.After(100 * time.Millisecond):
			// Exit code not available
			return -1, nil
		}
	case <-time.After(timeout):
		return 0, fmt.Errorf("timeout waiting for process to exit")
	}
}
