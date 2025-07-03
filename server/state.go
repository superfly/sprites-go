package main

import (
	"context"
)

// IsProcessRunning returns whether the supervised process is running
func (s *System) IsProcessRunning() bool {
	return s.getState("processRunning").(bool)
}

// WaitForProcessRunning blocks until the process is running
// Returns immediately if already running
func (s *System) WaitForProcessRunning(ctx context.Context) error {
	if s.getState("processRunning").(bool) {
		return nil
	}
	ch := s.processReadyCh

	// Wait for process to be ready or context to be cancelled
	select {
	case <-ch:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	}
}

// IsJuiceFSReady returns whether JuiceFS is ready
func (s *System) IsJuiceFSReady() bool {
	return s.getState("juicefsReady").(bool)
}

// WaitForJuiceFS blocks until JuiceFS is ready
// Returns immediately if already ready or not configured
func (s *System) WaitForJuiceFS(ctx context.Context) error {
	// If JuiceFS is not configured, it's "ready" (nothing to wait for)
	if s.juicefs == nil {
		return nil
	}
	if s.getState("juicefsReady").(bool) {
		return nil
	}
	ch := s.juicefsReadyCh

	// Wait for JuiceFS to be ready or context to be cancelled
	select {
	case <-ch:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	}
}

// IsRestoring returns whether the system is currently restoring
func (s *System) IsRestoring() bool {
	return s.getState("restoringNow").(bool)
}

// HasJuiceFS returns whether JuiceFS is configured
func (s *System) HasJuiceFS() bool {
	return s.juicefs != nil
}
