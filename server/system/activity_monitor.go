package system

import (
    "context"
    "fmt"
    "log/slog"
    "net"
    "net/http"
    "os"
    "sync"
    "sync/atomic"
    "time"

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
	activeCount  int64 // atomic counter for active activities
	lastActivity time.Time
	suspendedAt  time.Time // timestamp when suspend occurred

	// Internal channels
	activityCh chan activityEvent
	stopCh     chan struct{}
	errCh      chan error // Reports panics from goroutines

	// Ensure Stop() is idempotent
	stopOnce sync.Once
}

type activityEvent struct {
	isStart bool
	source  string // "http" or "exec" for debugging
}

func NewActivityMonitor(ctx context.Context, sys *System, idleAfter time.Duration) *ActivityMonitor {
	return &ActivityMonitor{
		logger:       tap.Logger(ctx),
		system:       sys,
		idleAfter:    idleAfter,
		activityCh:   make(chan activityEvent, 128),
		stopCh:       make(chan struct{}),
		errCh:        make(chan error, 1), // Buffered to avoid blocking on panic
		lastActivity: time.Now(),
	}
}

func (m *ActivityMonitor) Start(ctx context.Context) {
	tap.Go(m.logger, m.errCh, func() {
		m.run(ctx)
	})
}

// Stop immediately stops the activity monitor loop to prevent further suspend attempts
func (m *ActivityMonitor) Stop() {
	m.stopOnce.Do(func() {
		close(m.stopCh)
	})
}

// ActivityStarted increments the activity counter
func (m *ActivityMonitor) ActivityStarted(source string) {
	atomic.AddInt64(&m.activeCount, 1)
	select {
	case m.activityCh <- activityEvent{isStart: true, source: source}:
	default:
		m.logger.Debug("Activity channel full, event dropped", "source", source)
	}
}

// ActivityEnded decrements the activity counter
func (m *ActivityMonitor) ActivityEnded(source string) {
	atomic.AddInt64(&m.activeCount, -1)
	select {
	case m.activityCh <- activityEvent{isStart: false, source: source}:
	default:
		m.logger.Debug("Activity channel full, event dropped", "source", source)
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


// makeFlapsRequest is a helper function to make requests to the Flaps API
func (m *ActivityMonitor) makeFlapsRequest(ctx context.Context, method, path string) (*http.Response, error) {
    d := &net.Dialer{Timeout: 2 * time.Second}
    tr := &http.Transport{
        DialContext: func(c context.Context, network, addr string) (net.Conn, error) {
            return d.DialContext(c, "unix", "/.fly/api")
        },
    }
    client := &http.Client{Transport: tr, Timeout: 5 * time.Second}

    app := os.Getenv("FLY_APP_NAME")
    mid := os.Getenv("FLY_MACHINE_ID")
    url := fmt.Sprintf("http://flaps/v1/apps/%s%s", app, fmt.Sprintf(path, mid))

    req, err := http.NewRequestWithContext(ctx, method, url, nil)
    if err != nil {
        return nil, err
    }

    return client.Do(req)
}


// handleActivityEvent processes an activity event and updates internal state.
func (m *ActivityMonitor) handleActivityEvent(ev activityEvent) {
	currentCount := atomic.LoadInt64(&m.activeCount)

	if ev.isStart {
		m.logger.Debug("Activity started", "source", ev.source, "active_count", currentCount)
	} else {
		m.logger.Debug("Activity ended", "source", ev.source, "active_count", currentCount)
		m.lastActivity = time.Now()
	}
}

func (m *ActivityMonitor) run(ctx context.Context) {
	var idleTimer *time.Timer
	var idleTimerCh <-chan time.Time

	// If a main process is configured, wait until it's started before
	// enabling the idle timer. This avoids suspend attempts during boot.
	if m.system != nil && m.system.config != nil && len(m.system.config.ProcessCommand) > 0 {
		// Poll until process is running or context is cancelled
		for !m.system.IsProcessRunning() {
			select {
			case <-ctx.Done():
				return
			case <-time.After(100 * time.Millisecond):
			}
		}
	}

	// Start idle timer if there is no active activity after process start (if any)
	currentCount := atomic.LoadInt64(&m.activeCount)
	if currentCount == 0 {
		idleTimer = time.NewTimer(m.idleAfter)
		idleTimerCh = idleTimer.C
		m.logger.Debug("Starting idle timer", "duration", m.idleAfter)
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

		case ev := <-m.activityCh:
			m.handleActivityEvent(ev)
			currentCount := atomic.LoadInt64(&m.activeCount)

			if ev.isStart {
				// Cancel idle timer if running
				if idleTimer != nil {
					if !idleTimer.Stop() {
						// Timer already fired, drain the channel
						select {
						case <-idleTimer.C:
						default:
						}
					}
					idleTimer = nil
					idleTimerCh = nil
				}
			} else {
				// Start idle timer if no more activities
				if currentCount == 0 && idleTimer == nil {
					idleTimer = time.NewTimer(m.idleAfter)
					idleTimerCh = idleTimer.C
					m.logger.Debug("Started idle timer", "duration", m.idleAfter)
				}
			}

		case <-idleTimerCh:
			// Timer expired, check if still idle
			currentCount := atomic.LoadInt64(&m.activeCount)
			m.logger.Debug("Idle timer expired", "active_count", currentCount)

			if currentCount == 0 {
				// No active activities, start suspend in a goroutine
				suspendCtx, suspendCancel := context.WithCancel(context.Background())
				suspendDone := make(chan struct{})

				tap.Go(m.logger, m.errCh, func() {
					defer close(suspendDone)
					m.suspend(suspendCtx, time.Since(m.lastActivity))
				})

				// Wait for suspend to complete or for activity to be detected
			suspendLoop:
				for {
					select {
					case ev := <-m.activityCh:
						// Activity detected during suspend, cancel it
						currentCount := atomic.LoadInt64(&m.activeCount)
						m.logger.Info("Activity detected during suspend, cancelling",
							"source", ev.source, "active_count", currentCount, "is_start", ev.isStart)
						suspendCancel()

						// Process the activity event normally
						m.handleActivityEvent(ev)

						// Continue draining activity events until suspend is done
						// Don't break out of suspendLoop yet

					case <-suspendDone:
						// Suspend completed (either successfully or cancelled)
						break suspendLoop
					}
				}

				suspendCancel() // Ensure context is cancelled
				idleTimer = nil
				idleTimerCh = nil

				// Restart the idle timer after suspend completes (or if cancelled)
				// This allows repeated suspensions if the system remains idle
				currentCount = atomic.LoadInt64(&m.activeCount)
				if currentCount == 0 {
					m.lastActivity = time.Now()
					idleTimer = time.NewTimer(m.idleAfter)
					idleTimerCh = idleTimer.C
					m.logger.Debug("Restarted idle timer after suspend", "duration", m.idleAfter)
				}
			} else {
				idleTimer = nil
				idleTimerCh = nil
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

	// Sync filesystem and get unfreeze function
	start := time.Now()
	syncCtx, syncCancel := context.WithTimeout(ctx, 10*time.Second)
	defer syncCancel()

	unfreezeFunc, syncErr := m.system.SyncOverlay(syncCtx)
	if syncErr != nil {
		if ctx.Err() != nil {
			m.logger.Info("Overlay sync cancelled", "error", syncErr)
			return cleanup, true, ctx.Err()
		}
		m.logger.Error("Overlay sync failed", "error", syncErr)
		return cleanup, false, syncErr
	}
	m.logger.Debug("Overlay sync completed", "duration_s", time.Since(start).Seconds())

	// Add cleanup to unfreeze filesystem
	if unfreezeFunc != nil {
		cleanupFuncs = append(cleanupFuncs, unfreezeFunc)
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
	m.suspendedAt = time.Now()

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
	cleanup, wasCancelled, err := m.prepSuspend(ctx)
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
	initialSystemTime := time.Now()
    m.logger.Debug("Starting suspend process", "initial_time", initialSystemTime.Format(time.RFC3339Nano))

    // Call flaps suspend API
    apiStart := time.Now()
    resp, err := m.makeFlapsRequest(apiCtx, http.MethodPost, "/machines/%s/suspend")
    apiDuration := time.Since(apiStart)

    if err != nil {
        m.logger.Error("Failed to call suspend API", "error", err, "duration", apiDuration)
    } else if resp != nil {
        m.logger.Info("Suspend API response",
            "status", resp.StatusCode,
            "duration", apiDuration,
            "status_text", resp.Status)
        if resp.Body != nil {
            resp.Body.Close()
        }
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
