package main

import (
	"context"
)

// IsProcessRunning returns whether the supervised process is running
func (s *System) IsProcessRunning() bool {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return s.processRunning
}

// WaitForProcessRunning blocks until the process is running
// Returns immediately if already running
func (s *System) WaitForProcessRunning(ctx context.Context) error {
	s.mu.RLock()
	if s.processRunning {
		s.mu.RUnlock()
		return nil
	}
	ch := s.processReadyCh
	s.mu.RUnlock()

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
	s.mu.RLock()
	defer s.mu.RUnlock()
	return s.juicefsReady
}

// WaitForJuiceFS blocks until JuiceFS is ready
// Returns immediately if already ready or not configured
func (s *System) WaitForJuiceFS(ctx context.Context) error {
	s.mu.RLock()
	// If JuiceFS is not configured, it's "ready" (nothing to wait for)
	if s.juicefs == nil {
		s.mu.RUnlock()
		return nil
	}
	if s.juicefsReady {
		s.mu.RUnlock()
		return nil
	}
	ch := s.juicefsReadyCh
	s.mu.RUnlock()

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
	s.mu.RLock()
	defer s.mu.RUnlock()
	return s.restoringNow
}

// HasJuiceFS returns whether JuiceFS is configured
func (s *System) HasJuiceFS() bool {
	return s.juicefs != nil
}
