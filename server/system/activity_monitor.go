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

// checkApiTime checks for time divergence between local and API server time
// Returns true if resume is detected, false otherwise
func (m *ActivityMonitor) checkApiTime(loopCount int) bool {
	// Get current system time before API call
	apiCheckTime := time.Now()

	// Make metadata request
	ctx, cancel := context.WithTimeout(context.Background(), 3*time.Second)
	resp, err := m.makeFlapsRequest(ctx, http.MethodGet, "/machines/%s/metadata")
	cancel()

	if err != nil {
		m.logger.Debug("Failed to get metadata", "error", err, "loop", loopCount)
		return false
	}

	if resp == nil {
		return false
	}

	// Parse Date header
	dateStr := resp.Header.Get("Date")
	resp.Body.Close()

	if dateStr == "" {
		m.logger.Debug("No Date header in metadata response", "loop", loopCount)
		return false
	}

	serverTime, err := http.ParseTime(dateStr)
	if err != nil {
		m.logger.Debug("Failed to parse Date header", "error", err, "date", dateStr, "loop", loopCount)
		return false
	}

	// Compare server time with local time
	timeDiff := serverTime.Sub(apiCheckTime).Abs()
	timeDiffMs := timeDiff.Milliseconds()

	m.logger.Debug("API time check",
		"loop", loopCount,
		"local_time", apiCheckTime.Format(time.RFC3339),
		"server_time", serverTime.Format(time.RFC3339),
		"time_diff_ms", timeDiffMs)

	// If server and local time diverge by more than 2 seconds, resume detected
	if timeDiff > 2*time.Second {
		m.logger.Info("Resume detected via API time divergence",
			"loops", loopCount,
			"local_time", apiCheckTime.Format(time.RFC3339),
			"server_time", serverTime.Format(time.RFC3339),
			"divergence_ms", timeDiffMs)
		return true
	}

	return false
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
		m.logger.Info("Starting idle timer", "duration", m.idleAfter)
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
			currentCount := atomic.LoadInt64(&m.activeCount)

			if ev.isStart {
				// Activity started
				m.logger.Debug("Activity started", "source", ev.source, "active_count", currentCount)

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
				// Activity ended
				m.logger.Debug("Activity ended", "source", ev.source, "active_count", currentCount)
				m.lastActivity = time.Now()

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
				// No active activities, suspend
				m.suspend(time.Since(m.lastActivity))
				idleTimer = nil
				idleTimerCh = nil
			} else {
				idleTimer = nil
				idleTimerCh = nil
			}
		}
	}
}

func (m *ActivityMonitor) suspend(inactive time.Duration) {
	// Check if suspend should be prevented
	preventSuspend := os.Getenv("SPRITE_PREVENT_SUSPEND") == "true"

	// Store the timestamp when suspension started
	m.suspendedAt = time.Now()

	if m.admin != nil {
		m.admin.SendActivityEvent("suspend", map[string]interface{}{
			"inactive_ms": inactive.Milliseconds(),
		})
	}

	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	if preventSuspend {
		m.logger.Info("ActivityMonitor: would suspend but SPRITE_PREVENT_SUSPEND=true", "idle_s", inactive.Seconds())
	} else {
		m.logger.Info("ActivityMonitor: suspending", "idle_s", inactive.Seconds())
	}

	// Sync filesystem and get unfreeze function
	start := time.Now()
	unfreezeFunc, err := m.system.SyncOverlay(ctx)
	if err != nil {
		m.logger.Debug("overlay sync error", "error", err)
	}
	m.logger.Info("Suspending, fs sync completed", "duration_s", time.Since(start).Seconds())

	// Stop litestream replication before suspend to ensure everything is flushed
	if m.system.DBManager != nil {
		m.logger.Info("Stopping litestream before suspend")
		stopStart := time.Now()
		if err := m.system.DBManager.StopLitestream(ctx); err != nil {
			m.logger.Error("Failed to stop litestream", "error", err)
		} else {
			m.logger.Info("Litestream stopped", "duration_s", time.Since(stopStart).Seconds())
		}
	}

	// Defer unfreeze and litestream restart to run after suspend/resume detection
	defer func() {
		if unfreezeFunc != nil {
			if err := unfreezeFunc(); err != nil {
				m.logger.Error("Failed to unfreeze filesystem after resume", "error", err)
			} else {
				m.logger.Info("Filesystem unfrozen after resume")
			}
		} else {
			m.logger.Debug("Skipping unfreeze after resume: overlay not prepared or SyncOverlay failed")
		}

		// Restart litestream async after resume
		if m.system.DBManager != nil {
			m.logger.Info("Restarting litestream after resume")
			tap.Go(m.logger, m.errCh, func() {
				restartCtx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
				defer cancel()
				restartStart := time.Now()
				if err := m.system.DBManager.StartLitestream(restartCtx); err != nil {
					m.logger.Error("Failed to restart litestream", "error", err)
				} else {
					m.logger.Info("Litestream restarted", "duration_s", time.Since(restartStart).Seconds())
				}
			})
		}
	}()

	// Skip the actual suspend API call and wait loop if prevented
	if preventSuspend {
		m.logger.Info("Suspend prevented by SPRITE_PREVENT_SUSPEND=true, continuing to run")
		return
	}

	// Capture system wall time BEFORE the suspend API call
	initialSystemTime := time.Now()
	m.logger.Info("Starting suspend process", "initial_time", initialSystemTime.Format(time.RFC3339Nano))

	// Call flaps suspend API
	m.logger.Info("Calling Fly suspend API")

	apiStart := time.Now()
	resp, err := m.makeFlapsRequest(ctx, http.MethodPost, "/machines/%s/suspend")
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
