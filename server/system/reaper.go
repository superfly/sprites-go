package system

import (
	"context"
	"log/slog"
	"os"
	"os/signal"
	"sync"
	"syscall"
	"time"

	"github.com/superfly/sprite-env/pkg/tap"
)

// Reaper handles reaping of zombie processes
// When running as PID 1, it reaps all orphaned processes in the system
// When not PID 1, it reaps direct children to prevent zombies
type Reaper struct {
	logger *slog.Logger
	ctx    context.Context
	cancel context.CancelFunc
	done   chan struct{}

	// Reap event tracking
	mu        sync.RWMutex
	events    map[int]time.Time // Map of PID to reap time
	listeners []chan int        // Channels listening for reap events

	// Ensure Start is only called once
	started   bool
	startOnce sync.Once
}

// NewReaper creates a new Reaper instance
func NewReaper(ctx context.Context) *Reaper {
	ctx, cancel := context.WithCancel(ctx)
	return &Reaper{
		logger:    tap.Logger(ctx),
		ctx:       ctx,
		cancel:    cancel,
		done:      make(chan struct{}),
		events:    make(map[int]time.Time),
		listeners: make([]chan int, 0),
	}
}

// Start starts the zombie reaper
// When running as PID 1, it reaps all orphaned processes
// When not PID 1, it still reaps direct children to prevent zombies
//
// Safety guarantees:
// - syscall.Wait4 uses WNOHANG flag, so it never blocks
// - The goroutine listens for context cancellation and exits cleanly
// - Signal handler is properly cleaned up with signal.Stop()
// - Can only be started once to prevent channel panics
func (r *Reaper) Start() {
	r.startOnce.Do(func() {
		isPID1 := os.Getpid() == 1
		if isPID1 {
			r.logger.Info("Running as PID 1, starting zombie reaper for all orphaned processes")
		} else {
			r.logger.Info("Not PID 1, starting reaper for direct children only")
		}

		// Create a separate signal channel for SIGCHLD
		sigchldCh := make(chan os.Signal, 10)
		signal.Notify(sigchldCh, syscall.SIGCHLD)

		go func() {
			defer close(r.done)
			defer signal.Stop(sigchldCh)

			for {
				select {
				case <-r.ctx.Done():
					r.logger.Debug("Reaper context cancelled, stopping")
					return
				case <-sigchldCh:
					// Reap all available zombie processes
					for {
						var status syscall.WaitStatus
						pid, err := syscall.Wait4(-1, &status, syscall.WNOHANG, nil)
						if err != nil {
							// ECHILD is expected when there are no child processes
							if err != syscall.ECHILD {
								r.logger.Debug("Error during wait4", "error", err)
							}
							break
						}
						if pid <= 0 {
							// No more zombies to reap
							break
						}
						if isPID1 {
							r.logger.Debug("Reaped zombie process", "pid", pid, "status", status)
						} else {
							r.logger.Debug("Reaped direct child process", "pid", pid, "status", status)
						}

						// Emit reap event
						r.emitEvent(pid)
					}
				}
			}
		}()
		r.started = true
	})
}

// Stop stops the zombie reaper
func (r *Reaper) Stop(timeout time.Duration) error {
	r.cancel()

	// Wait for reaper to finish with timeout
	select {
	case <-r.done:
		r.logger.Debug("Zombie reaper stopped cleanly")
		return nil
	case <-time.After(timeout):
		r.logger.Warn("Zombie reaper did not stop within timeout")
		return nil
	}
}

// SubscribeToEvents creates a channel that receives PIDs when processes are reaped
func (r *Reaper) SubscribeToEvents() <-chan int {
	r.mu.Lock()
	defer r.mu.Unlock()

	ch := make(chan int, 10)
	r.listeners = append(r.listeners, ch)
	return ch
}

// UnsubscribeFromEvents removes a reap event listener
func (r *Reaper) UnsubscribeFromEvents(ch <-chan int) {
	r.mu.Lock()
	defer r.mu.Unlock()

	for i, listener := range r.listeners {
		if listener == ch {
			// Remove the listener and close it
			close(listener)
			r.listeners = append(r.listeners[:i], r.listeners[i+1:]...)
			break
		}
	}
}

// WasProcessReaped checks if a process with the given PID was reaped
func (r *Reaper) WasProcessReaped(pid int) (bool, time.Time) {
	r.mu.RLock()
	defer r.mu.RUnlock()

	reapTime, found := r.events[pid]
	return found, reapTime
}

// emitEvent notifies all listeners that a process was reaped
func (r *Reaper) emitEvent(pid int) {
	r.mu.Lock()
	defer r.mu.Unlock()

	// Record the reap event
	r.events[pid] = time.Now()

	// Clean up old events if map gets too large (keep last 1000)
	if len(r.events) > 1000 {
		// Find oldest events to remove
		var oldestPIDs []int
		for p := range r.events {
			oldestPIDs = append(oldestPIDs, p)
			if len(oldestPIDs) > 100 { // Remove 100 oldest
				break
			}
		}
		for _, p := range oldestPIDs {
			delete(r.events, p)
		}
	}

	// Notify all listeners
	for _, ch := range r.listeners {
		select {
		case ch <- pid:
			// Sent successfully
		default:
			// Channel is full, skip
		}
	}
}

// Reaper delegation methods

// SubscribeToReapEvents delegates to the reaper
func (s *System) SubscribeToReapEvents() <-chan int {
	if s.Reaper != nil {
		return s.Reaper.SubscribeToEvents()
	}
	// Return a closed channel if no reaper
	ch := make(chan int)
	close(ch)
	return ch
}

// UnsubscribeFromReapEvents delegates to the reaper
func (s *System) UnsubscribeFromReapEvents(ch <-chan int) {
	if s.Reaper != nil {
		s.Reaper.UnsubscribeFromEvents(ch)
	}
}

// WasProcessReaped checks if a process with given PID was reaped
func (s *System) WasProcessReaped(pid int) (bool, time.Time) {
	if s.Reaper == nil {
		return false, time.Time{}
	}
	return s.Reaper.WasProcessReaped(pid)
}
