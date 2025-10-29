package services

import (
	"context"
	"fmt"
	"io"
	"os"
	"sync"
	"syscall"
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

// ProgressReporter allows services to report progress during start/stop
// This prevents false-positive hung detection for long-running operations
type ProgressReporter interface {
	// ReportProgress indicates the service is making progress with a status message
	// This resets the hung detection timer
	ReportProgress(message string)
}

// ManagedService represents a service that can be started/stopped
// This interface allows wrapping Go modules (like DBManager, JuiceFS) as services
type ManagedService interface {
    Start(ctx context.Context, progress ProgressReporter) error
    Stop(ctx context.Context, progress ProgressReporter) error
}

// ServiceHooks allows registering start/stop logic without a concrete type
type ServiceHooks struct {
    Start func(ctx context.Context, progress ProgressReporter) error
    Stop  func(ctx context.Context, progress ProgressReporter) error
}

// ServiceDefinition wraps either a process-based or managed service
// This allows the service manager to handle both types uniformly
type ServiceDefinition struct {
	Name         string
	Dependencies []string // Services that must start before this one

	// Optional timeout override (0 = use default of 2 minutes)
	// For services that may take a long time but report progress
	MaxHungDuration time.Duration // Max time without progress before considered hung

    // One of these must be set:
    ProcessService *Service       // Process-based service (existing)
    ManagedService ManagedService // Go module service (new)
    Hooks          *ServiceHooks  // Inline lifecycle hooks (preferred to avoid wrappers)
}

// processExists checks if a process with the given PID is still running
func processExists(pid int) bool {
	process, err := os.FindProcess(pid)
	if err != nil {
		return false
	}
	// On Unix, FindProcess always succeeds, so we need to send signal 0 to check
	err = process.Signal(syscall.Signal(0))
	return err == nil
}
