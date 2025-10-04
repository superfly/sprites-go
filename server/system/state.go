package system

import (
	"context"
	"fmt"
	"syscall"
)

// IsProcessRunning returns true if the process is currently running
func (s *System) IsProcessRunning() bool {
	if s.processCmd == nil || s.processCmd.Process == nil {
		return false
	}

	// Check if the process still exists by sending signal 0
	// Signal 0 doesn't actually send a signal, it just checks if the process exists
	err := syscall.Kill(s.processCmd.Process.Pid, 0)
	return err == nil
}

// ProcessPID returns the PID of the running process, or 0 if no process is running
func (s *System) ProcessPID() int {
	if s.processCmd == nil || s.processCmd.Process == nil {
		return 0
	}
	return s.processCmd.Process.Pid
}

// WhenProcessRunning waits until the process is running or returns immediately if already running.
// Returns an error if the context is cancelled before the process starts.
func (s *System) WhenProcessRunning(ctx context.Context) error {
	// No mutex needed - just select directly on the field
	select {
	case <-s.processRunningCh:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	}
}

// WhenProcessStopped waits until the process has stopped or returns immediately if not running.
// Returns an error if the context is cancelled before the process stops.
func (s *System) WhenProcessStopped(ctx context.Context) error {
	// No mutex needed - just select directly on the field
	select {
	case <-s.processStoppedCh:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	}
}

// WhenServiceManagerStopped waits until the services manager has fully stopped
// or returns immediately if it is not running. Returns an error if the context
// is cancelled before the services manager stops.
func (s *System) WhenServiceManagerStopped(ctx context.Context) error {
	// No mutex needed - just select directly on the field
	select {
	case <-s.servicesManagerStoppedCh:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	}
}

// WhenStorageReady waits until both JuiceFS and Overlay are ready or returns immediately if already ready.
// Returns an error if the context is cancelled before storage is ready.
func (s *System) WhenStorageReady(ctx context.Context) error {
	// Wait for JuiceFS to be ready
	if s.JuiceFS != nil {
		if err := s.JuiceFS.WhenReady(ctx); err != nil {
			return fmt.Errorf("JuiceFS not ready: %w", err)
		}
	}

	// Wait for Overlay to be ready
	if s.OverlayManager != nil {
		if err := s.OverlayManager.WhenReady(ctx); err != nil {
			return fmt.Errorf("Overlay not ready: %w", err)
		}
	}

	return nil
}

// WaitForJuiceFS waits for JuiceFS to be ready - deprecated, use WhenStorageReady instead
func (s *System) WaitForJuiceFS(ctx context.Context) error {
	return s.WhenStorageReady(ctx)
}

// WaitForOverlay waits for overlay to be ready - deprecated, use WhenStorageReady instead
func (s *System) WaitForOverlay(ctx context.Context) error {
	return s.WhenStorageReady(ctx)
}
