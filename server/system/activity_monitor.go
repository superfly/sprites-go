package system

import (
	"context"
	"log/slog"
	"os"
	"sync"
	"sync/atomic"
	"time"

	"github.com/superfly/sprite-env/pkg/fly"
	"github.com/superfly/sprite-env/pkg/tap"
)

// Context key for storing activity monitor
type activityMonitorKey struct{}

type ActivityMonitor struct {
	logger    *slog.Logger
	system    *System
	idleAfter time.Duration
	admin     *AdminChannel

	// Activity tracking
	lastActivity time.Time
	suspendedAt  time.Time // timestamp when suspend occurred

	// Registry of active sources (only accessed by run loop)
	activities map[string]struct{}

	// Activity event channel for coordinating with run loop
	activityEventCh chan activityEvent

	// Internal channels
	stopCh chan struct{}
	errCh  chan error // Reports panics from goroutines

	// Ensure Stop() is idempotent
	stopOnce sync.Once

	// started indicates whether the run loop is active; used to gate event APIs
	started atomic.Bool

	// Injection seams for testing
	prepSuspendFn func(ctx context.Context) (cleanup func(), cancelled bool, err error)
	suspendAPIFn  func(ctx context.Context) error
	now           func() time.Time

	// Callback invoked right before calling suspend API (point of no return)
	onSuspendCommit func()
}

type activityEvent struct {
	isStart bool
	source  string // "http:<id>", "tmux:<session>", "boot", "socket", etc.
}

func NewActivityMonitor(ctx context.Context, sys *System, idleAfter time.Duration) *ActivityMonitor {
	m := &ActivityMonitor{
		logger:          tap.Logger(ctx),
		system:          sys,
		idleAfter:       idleAfter,
		activities:      make(map[string]struct{}),
		activityEventCh: make(chan activityEvent, 100), // Buffered for burst handling
		stopCh:          make(chan struct{}),
		errCh:           make(chan error, 1), // Buffered to avoid blocking on panic
		lastActivity:    time.Now(),
	}
	// Set default injection seams
	m.prepSuspendFn = m.prepSuspend
	m.suspendAPIFn = fly.Suspend
	m.now = time.Now
	m.onSuspendCommit = func() {}
	return m
}

func (m *ActivityMonitor) Start(ctx context.Context) {
	// Quiet by default – use Debug for startup visibility
	m.logger.Debug("ActivityMonitor: starting", "idle_after", m.idleAfter)
	// Mark as started before launching the run loop so producers can proceed
	m.started.Store(true)
	tap.Go(m.logger, m.errCh, func() {
		m.run(ctx)
	})
}

// Stop immediately stops the activity monitor loop to prevent further suspend attempts
func (m *ActivityMonitor) Stop() {
	m.stopOnce.Do(func() {
		// Prevent new events from enqueueing; non-blocking APIs will drop
		m.started.Store(false)
		close(m.stopCh)
	})
}

// ActivityStarted records the start of an activity and signals the monitor
func (m *ActivityMonitor) ActivityStarted(source string) {
	// Reject events if the monitor isn't running
	if !m.started.Load() {
		m.logger.Info("ActivityMonitor: drop event - not started", "source", source)
		return
	}
	// Non-blocking send to avoid deadlocks/backpressure cascades
	select {
	case m.activityEventCh <- activityEvent{isStart: true, source: source}:
		m.logger.Debug("ActivityMonitor: activity started", "source", source)
	default:
		m.logger.Warn("ActivityMonitor: drop event - buffer full", "source", source)
	}
}

// ActivityEnded records the end of an activity
func (m *ActivityMonitor) ActivityEnded(source string) {
	// Reject events if the monitor isn't running
	if !m.started.Load() {
		m.logger.Info("ActivityMonitor: drop event - not started", "source", source)
		return
	}
	// Non-blocking send to avoid deadlocks/backpressure cascades
	select {
	case m.activityEventCh <- activityEvent{isStart: false, source: source}:
		m.logger.Debug("ActivityMonitor: activity ended", "source", source)
	default:
		m.logger.Warn("ActivityMonitor: drop event - buffer full", "source", source)
	}
}

// SetAdminChannel sets the admin channel for sending events
func (m *ActivityMonitor) SetAdminChannel(admin *AdminChannel) {
	m.admin = admin
}

// Wait blocks until the run goroutine completes or panics
func (m *ActivityMonitor) Wait() error {
	// Activity monitor doesn't have a done channel, so we only wait on errors
	// The run goroutine completes when the context is cancelled
	return <-m.errCh
}

// EnrichContext adds the activity monitor to the context for use by handlers
func (m *ActivityMonitor) EnrichContext(ctx context.Context) context.Context {
	// Add the monitor itself
	ctx = context.WithValue(ctx, activityMonitorKey{}, m)

	// Add a tracker function that handlers can use
	trackerFunc := func(isStart bool, source string) {
		if isStart {
			m.ActivityStarted(source)
		} else {
			m.ActivityEnded(source)
		}
	}
	ctx = context.WithValue(ctx, activityTrackerKey{}, trackerFunc)

	return ctx
}

// activityTrackerKey matches the one used in handlers package
type activityTrackerKey struct{}

func (m *ActivityMonitor) run(ctx context.Context) {
	var idleTimer *time.Timer
	var idleTimerCh <-chan time.Time
	var suspendCancel context.CancelFunc
	var suspendDoneCh chan struct{}
	var suspendCommitCh chan struct{}
	var suspendInProgress bool

	// Status reporter ticker
	statusTicker := time.NewTicker(60 * time.Second)
	defer statusTicker.Stop()

	// Start idle timer if there is no active activity
	if len(m.activities) == 0 {
		idleTimer = time.NewTimer(m.idleAfter)
		idleTimerCh = idleTimer.C
		// Log timer start at info level for visibility
		m.logger.Info("ActivityMonitor: starting idle timer", "duration", m.idleAfter)
	}

	for {
		select {
		case <-ctx.Done():
			if idleTimer != nil {
				idleTimer.Stop()
			}
			return

		case <-m.stopCh:
			if idleTimer != nil {
				idleTimer.Stop()
			}
			return

		case <-statusTicker.C:
			// Only report if we haven't suspended yet
			if m.suspendedAt.IsZero() {
				currentCount := len(m.activities)
				sources := make([]string, 0, len(m.activities))
				for source := range m.activities {
					sources = append(sources, source)
				}

				since := m.now().Sub(m.lastActivity)
				remaining := m.idleAfter - since
				if remaining < 0 {
					remaining = 0
				}

				m.logger.Info("ActivityMonitor: idle status",
					"active_count", currentCount,
					"sources", sources,
					"since_last_activity_s", since.Seconds(),
					"idle_after_s", m.idleAfter.Seconds(),
					"time_until_suspend_s", remaining.Seconds(),
				)
			}

		case event := <-m.activityEventCh:
			if event.isStart {
				// Add to registry
				wasEmpty := len(m.activities) == 0
				m.activities[event.source] = struct{}{}

				// If we had no activity and now we do, cancel idle timer
				if wasEmpty && idleTimer != nil {
					if !idleTimer.Stop() {
						select {
						case <-idleTimer.C:
						default:
						}
					}
					idleTimer = nil
					idleTimerCh = nil
					m.logger.Info("Activity detected, cancelling idle timer")
				}

				// Cancel suspend if in progress
				if suspendCancel != nil {
					m.logger.Info("Activity detected, cancelling suspend")
					suspendCancel()
					suspendCancel = nil
					if m.admin != nil {
						m.admin.SendActivityEvent("suspend_cancelled", map[string]interface{}{
							"reason": "activity_detected",
						})
					}
				} else if suspendInProgress {
					if m.admin != nil {
						m.admin.SendActivityEvent("activity_during_suspend", map[string]interface{}{
							"timestamp": m.now().Unix(),
						})
					}
				}

				m.lastActivity = m.now()
			} else {
				// Remove from registry
				delete(m.activities, event.source)

				// If registry is now empty, start idle timer
				if len(m.activities) == 0 && idleTimer == nil {
					idleTimer = time.NewTimer(m.idleAfter)
					idleTimerCh = idleTimer.C
					m.logger.Info("ActivityMonitor: started idle timer", "duration", m.idleAfter)
				}

				m.lastActivity = m.now()
			}

		case <-idleTimerCh:
			// Timer expired, check if still idle
			currentCount := len(m.activities)
			// Quiet default – debug-level
			m.logger.Debug("ActivityMonitor: idle timer expired", "active_count", currentCount)

			if currentCount == 0 {
				// Begin suspend flow
				suspendCtx, cancel := context.WithCancel(context.Background())
				suspendCancel = cancel
				suspendDoneCh = make(chan struct{})
				suspendCommitCh = make(chan struct{}, 1)

				// Arrange callback for commit point
				m.onSuspendCommit = func() {
					select {
					case suspendCommitCh <- struct{}{}:
					default:
					}
				}

				tap.Go(m.logger, m.errCh, func() {
					defer close(suspendDoneCh)
					m.suspend(suspendCtx, time.Since(m.lastActivity))
				})

				// Clear idle timer
				idleTimer = nil
				idleTimerCh = nil
			} else {
				idleTimer = nil
				idleTimerCh = nil
			}

		case <-suspendCommitCh:
			// Past point of no return
			suspendInProgress = true

		case <-suspendDoneCh:
			// Suspend completed (successfully or cancelled)
			suspendCancel = nil
			suspendDoneCh = nil
			suspendCommitCh = nil
			suspendInProgress = false

			// Restart idle timer if still idle
			if len(m.activities) == 0 {
				m.lastActivity = m.now()
				idleTimer = time.NewTimer(m.idleAfter)
				idleTimerCh = idleTimer.C
				m.logger.Debug("Restarted idle timer after suspend", "duration", m.idleAfter)
			}
		}
	}
}

// prepSuspend prepares the system for suspend synchronously.
// Returns a cleanup function (must always be called), cancelled flag, and error.
// The cleanup function handles post-resume or cancellation cleanup.
func (m *ActivityMonitor) prepSuspend(ctx context.Context) (cleanup func(), cancelled bool, err error) {
	var cleanupFuncs []func() error

	// Cleanup function calls all accumulated cleanup functions in order
	cleanup = func() {
		for _, fn := range cleanupFuncs {
			if err := fn(); err != nil {
				m.logger.Error("Cleanup function failed", "error", err)
			}
		}
	}

	m.logger.Info("Starting suspend preparation")

	// Flush cgroup metrics before suspend
	if m.system.ResourceMonitor != nil {
		m.system.ResourceMonitor.PreSuspend()
		// Add cleanup to call PostResume
		cleanupFuncs = append(cleanupFuncs, func() error {
			m.system.ResourceMonitor.PostResume()
			return nil
		})
	}

	// Freeze the container cgroup before sync
	if m.system.SpriteManager != nil {
		m.logger.Debug("Freezing container cgroup")
		if freezeErr := m.system.SpriteManager.Freeze(5 * time.Second); freezeErr != nil {
			m.logger.Error("Failed to freeze container cgroup", "error", freezeErr)
			// Non-fatal - continue with sync but without freeze
		} else {
			// Add cleanup to thaw the cgroup (runs on both cancel and resume)
			cleanupFuncs = append(cleanupFuncs, func() error {
				m.logger.Debug("Thawing container cgroup")
				thawStart := time.Now()
				if thawErr := m.system.SpriteManager.Thaw(5 * time.Second); thawErr != nil {
					m.logger.Error("Failed to thaw container cgroup", "error", thawErr)
					return thawErr
				}
				m.logger.Debug("Container cgroup thawed", "duration_s", time.Since(thawStart).Seconds())
				return nil
			})
		}
	}

	// Sync overlay filesystem (sync-only, no freeze)
	if m.system.OverlayManager != nil {
		start := time.Now()
		syncCtx, syncCancel := context.WithTimeout(ctx, 10*time.Second)
		defer syncCancel()

		if syncErr := m.system.OverlayManager.PrepareForCheckpoint(syncCtx); syncErr != nil {
			if ctx.Err() != nil {
				m.logger.Info("Overlay sync cancelled", "error", syncErr)
				return cleanup, true, ctx.Err()
			}
			m.logger.Error("Overlay sync failed", "error", syncErr)
			return cleanup, false, syncErr
		}
		m.logger.Debug("Overlay sync completed", "duration_s", time.Since(start).Seconds())
	}

	// Wait for JuiceFS writeback flush before suspend
	if m.system.JuiceFS != nil {
		flushStart := time.Now()
		fileCount, flushErr := m.system.JuiceFS.WaitForWritebackFlush(ctx)
		flushDuration := time.Since(flushStart)
		if flushErr != nil {
			if ctx.Err() != nil {
				m.logger.Info("JuiceFS writeback flush cancelled", "duration_s", flushDuration.Seconds())
				return cleanup, true, ctx.Err()
			}
			m.logger.Error("JuiceFS writeback flush failed", "error", flushErr, "duration_s", flushDuration.Seconds())
			return cleanup, false, flushErr
		} else if fileCount > 0 {
			m.logger.Info("JuiceFS writeback flush completed", "files", fileCount, "duration_s", flushDuration.Seconds())
		}
	}

	// Stop litestream replication before suspend to ensure everything is flushed
	if m.system.DBManager != nil {
		// Check if we've been cancelled before starting the stop operation
		if ctx.Err() != nil {
			return cleanup, true, ctx.Err()
		}

		m.logger.Debug("Stopping litestream before suspend")
		stopStart := time.Now()
		// Use non-cancellable context - once we start stopping, we must complete it
		stopCtx, stopCancel := context.WithTimeout(context.Background(), 60*time.Second)
		defer stopCancel()

		lsErr := m.system.DBManager.StopLitestream(stopCtx)

		// Add cleanup to restart litestream regardless of stop success/failure
		cleanupFuncs = append(cleanupFuncs, func() error {
			m.logger.Debug("Restarting litestream after resume")
			restartCtx, restartCancel := context.WithTimeout(context.Background(), 30*time.Second)
			defer restartCancel()
			return m.system.DBManager.StartLitestream(restartCtx)
		})

		// Now check if stop failed and return error
		if lsErr != nil {
			m.logger.Error("Failed to stop litestream", "error", lsErr)
			return cleanup, false, lsErr
		}
		m.logger.Debug("Litestream stopped", "duration_s", time.Since(stopStart).Seconds())
	}

	m.logger.Info("Suspend preparation complete")
	return cleanup, false, nil
}

func (m *ActivityMonitor) suspend(ctx context.Context, inactive time.Duration) {
	// Check if suspend should be prevented
	preventSuspend := os.Getenv("SPRITE_PREVENT_SUSPEND") == "true"

	// Store the timestamp when suspension started
	m.suspendedAt = m.now()

	if m.admin != nil {
		m.admin.SendActivityEvent("suspend", map[string]interface{}{
			"inactive_ms": inactive.Milliseconds(),
		})
	}

	if preventSuspend {
		m.logger.Info("ActivityMonitor: would suspend but SPRITE_PREVENT_SUSPEND=true", "idle_s", inactive.Seconds())
		return
	}

	m.logger.Info("ActivityMonitor: suspending", "idle_s", inactive.Seconds())

	// Prepare for suspend (sync filesystem, flush juicefs, stop litestream)
	cleanup, wasCancelled, err := m.prepSuspendFn(ctx)
	defer cleanup()

	if wasCancelled {
		m.logger.Info("Activity detected during suspend preparation, cancelling")
		return
	}

	if err != nil {
		m.logger.Error("Suspend preparation failed, aborting suspend", "error", err)
		return
	}

	apiCtx, apiCancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer apiCancel()

	// Capture system wall time BEFORE the suspend API call
	initialSystemTime := m.now()
	m.logger.Debug("Starting suspend process", "initial_time", initialSystemTime.Format(time.RFC3339Nano))

	// Call fly suspend API
	m.logger.Info("Calling Fly suspend API")

	// Notify run loop that we are past the point of no return
	if m.onSuspendCommit != nil {
		m.onSuspendCommit()
	}

	apiStart := time.Now()
	err = m.suspendAPIFn(apiCtx)
	apiDuration := time.Since(apiStart)

	if err != nil {
		m.logger.Error("Failed to call suspend API", "error", err, "duration", apiDuration)
	} else {
		m.logger.Info("Suspend API completed successfully", "duration", apiDuration)
	}

	// Start loop after suspend API call for resume detection
	const sleepInterval = 500 * time.Millisecond
	const maxLoopCount = 30
	loopCount := 0
	var actualElapsedHistory []int64 // Track actual elapsed time per loop

	for {
		loopCount++
		time.Sleep(sleepInterval)

		// Check for time divergence
		currentSystemTime := time.Now()

		// Note: time.Sub() uses monotonic time which doesn't include suspended time
		// So actualElapsed will only show time the process was actually running
		actualElapsed := currentSystemTime.Sub(initialSystemTime)

		// Track actual elapsed time (monotonic)
		actualElapsedHistory = append(actualElapsedHistory, actualElapsed.Milliseconds())

		// Additional debug: calculate wall clock difference in seconds
		wallClockDiff := currentSystemTime.Unix() - initialSystemTime.Unix()

		// Calculate expected loops based on wall clock time (not monotonic time)
		// This properly accounts for time spent suspended
		wallClockElapsed := time.Duration(wallClockDiff) * time.Second
		expectedLoops := int(wallClockElapsed / sleepInterval)
		loopDivergence := expectedLoops - loopCount

		// Only log debug on loops 2, 22, 42, etc
		if loopCount == 2 || (loopCount > 2 && (loopCount-2)%20 == 0) {
			m.logger.Debug("Resume detection loop",
				"loop", loopCount,
				"initial_time", initialSystemTime.Format(time.RFC3339Nano),
				"current_time", currentSystemTime.Format(time.RFC3339Nano),
				"actual_elapsed_ms", actualElapsed.Milliseconds(),
				"wall_clock_diff_s", wallClockDiff,
				"expected_loops", expectedLoops,
				"loop_divergence", loopDivergence,
				"elapsed_history", actualElapsedHistory)
		}

		// If we have fewer loops than expected, resume detected
		if loopDivergence >= 1 {
			m.logger.Info("Resume detected via loop divergence",
				"loops", loopCount,
				"initial_time", initialSystemTime.Format(time.RFC3339Nano),
				"current_time", currentSystemTime.Format(time.RFC3339Nano),
				"actual_elapsed_ms", actualElapsed.Milliseconds(),
				"wall_clock_diff_s", wallClockDiff,
				"expected_loops", expectedLoops,
				"loop_divergence", loopDivergence,
				"elapsed_history", actualElapsedHistory)

			// Send resume event to admin channel
			// Use wall clock time to get actual suspended duration
			suspendedDurationSec := currentSystemTime.Unix() - m.suspendedAt.Unix()
			if m.admin != nil {
				m.admin.SendActivityEvent("resume", map[string]interface{}{
					"suspended_duration_s": suspendedDurationSec,
					"source":               "wall_time",
				})
			}
			break
		}

		// On every other iteration, check API time
		// Commented out for now
		// if loopCount%2 == 0 {
		// 	if m.checkApiTime(loopCount) {
		// 		// Send resume event to admin channel
		// 		suspendedDuration := time.Since(m.suspendedAt)
		// 		if m.admin != nil {
		// 			m.admin.SendActivityEvent("resume", map[string]interface{}{
		// 				"suspended_duration_ms": suspendedDuration.Milliseconds(),
		// 				"source":                "fly_api_time",
		// 			})
		// 		}
		// 		break
		// 	}
		// }

		// Safety timeout
		if loopCount >= maxLoopCount {
			m.logger.Warn("Resume detection timeout reached",
				"loops", loopCount,
				"monotonic_elapsed", actualElapsed,
				"wall_clock_diff_s", wallClockDiff,
				"elapsed_history", actualElapsedHistory)
			break
		}
	}

	m.logger.Info("Resume detection complete")
}
