package system

import (
	"context"
	"fmt"
	"os"
	"time"
)

// emitAdminEvent is a small helper to safely push an event payload to the admin channel.
// It tolerates an uninitialized or disconnected channel.
func (s *System) emitAdminEvent(eventType string, payload map[string]interface{}) {
	if s.AdminChannel == nil {
		return
	}
	s.AdminChannel.Push(eventType, payload)
}

// runTimedStep runs fn while emitting start/complete admin events and periodic WARNs
// if the step takes longer than warnAfter; subsequent WARNs are emitted every warnEvery.
// It does not modify any provided contexts or timeouts; it is purely informational.
func (s *System) runTimedStep(ctx context.Context, phase string, step string, warnAfter, warnEvery time.Duration, fn func() error) error {
	start := time.Now()
	// Step start event
	s.emitAdminEvent(fmt.Sprintf("%s.step", phase), map[string]interface{}{
		"step":       step,
		"status":     "start",
		"started_at": start.UnixMilli(),
	})

	// Warning ticker goroutine
	done := make(chan struct{})
	if warnAfter > 0 && warnEvery > 0 {
		// Skip boot WARNs while explicit wait env toggles are set
		if phase == "boot" && (os.Getenv("WAIT_FOR_BOOT") == "true" || os.Getenv("WAIT_FOR_JUICEFS_READY") == "true") {
			// no warn ticker while paused intentionally
		} else {
			go func() {
				select {
				case <-time.After(warnAfter):
					// First WARN
					dur := time.Since(start)
					s.logger.Warn("Step taking longer than expected", "phase", phase, "step", step, "duration", dur)
					s.emitAdminEvent(fmt.Sprintf("%s.warn", phase), map[string]interface{}{
						"step":        step,
						"started_at":  start.UnixMilli(),
						"duration_ms": dur.Milliseconds(),
					})
					// Subsequent WARNs
					t := time.NewTicker(warnEvery)
					defer t.Stop()
					for {
						select {
						case <-t.C:
							d := time.Since(start)
							s.logger.Warn("Step still in progress", "phase", phase, "step", step, "duration", d)
							s.emitAdminEvent(fmt.Sprintf("%s.warn", phase), map[string]interface{}{
								"step":        step,
								"started_at":  start.UnixMilli(),
								"duration_ms": d.Milliseconds(),
							})
						case <-done:
							return
						case <-ctx.Done():
							return
						}
					}
				case <-done:
					return
				case <-ctx.Done():
					return
				}
			}()
		}
	}

	// Execute step
	err := fn()
	close(done)

	// Complete event
	finish := time.Now()
	payload := map[string]interface{}{
		"step":        step,
		"status":      "complete",
		"started_at":  start.UnixMilli(),
		"duration_ms": finish.Sub(start).Milliseconds(),
	}
	if err != nil {
		payload["status"] = "error"
		payload["error"] = err.Error()
	}
	s.emitAdminEvent(fmt.Sprintf("%s.step", phase), payload)
	return err
}
