package main

import (
	"context"
	"fmt"
	"log/slog"
	"net"
	"net/http"
	"os"
	"sync/atomic"
	"time"
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
	isSuspended  int32     // atomic: 0 = not suspended, 1 = suspended
	suspendedAt  time.Time // timestamp when suspend occurred

	// Internal channels
	activityCh chan activityEvent
	stopCh     chan struct{}
}

type activityEvent struct {
	isStart bool
	source  string // "http" or "exec" for debugging
}

func NewActivityMonitor(l *slog.Logger, sys *System, idleAfter time.Duration) *ActivityMonitor {
	return &ActivityMonitor{
		logger:       l,
		system:       sys,
		idleAfter:    idleAfter,
		activityCh:   make(chan activityEvent, 128),
		stopCh:       make(chan struct{}),
		lastActivity: time.Now(),
	}
}

func (m *ActivityMonitor) Start(ctx context.Context) {
	go m.run(ctx)
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

	// Start idle timer immediately at boot if no activity
	currentCount := atomic.LoadInt64(&m.activeCount)
	if currentCount == 0 {
		idleTimer = time.NewTimer(m.idleAfter)
		idleTimerCh = idleTimer.C
		m.logger.Info("Starting idle timer at boot", "duration", m.idleAfter)
	}

	for {
		select {
		case <-ctx.Done():
			if idleTimer != nil {
				idleTimer.Stop()
			}
			return

		case ev := <-m.activityCh:
			currentCount := atomic.LoadInt64(&m.activeCount)

			if ev.isStart {
				// Activity started
				m.logger.Debug("Activity started", "source", ev.source, "active_count", currentCount)

				// Handle resume if suspended - use atomic CAS to ensure only one goroutine sends resume
				if atomic.CompareAndSwapInt32(&m.isSuspended, 1, 0) {
					suspendedDuration := time.Since(m.suspendedAt)
					m.logger.Info("Resume detected", "source", ev.source, "duration_ms", suspendedDuration.Milliseconds())
					if m.admin != nil {
						m.admin.SendActivityEvent("resume", map[string]interface{}{
							"suspended_duration_ms": suspendedDuration.Milliseconds(),
							"source":                ev.source,
						})
					}
				}

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
				m.suspend(time.Since(m.lastActivity))
			}
			idleTimer = nil
			idleTimerCh = nil
		}
	}
}

func (m *ActivityMonitor) suspend(inactive time.Duration) {
	// Set suspended state atomically and store the timestamp
	atomic.StoreInt32(&m.isSuspended, 1)
	m.suspendedAt = time.Now()

	if m.admin != nil {
		m.admin.SendActivityEvent("suspend", map[string]interface{}{
			"inactive_ms": inactive.Milliseconds(),
		})
	}

	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	m.logger.Info("ActivityMonitor: suspending", "idle_s", inactive.Seconds())

	// Sync filesystem
	start := time.Now()
	if err := m.system.SyncOverlay(ctx); err != nil {
		m.logger.Debug("overlay sync error", "error", err)
	}
	m.logger.Info("Suspending, fs sync completed", "duration_s", time.Since(start).Seconds())

	// Call flaps suspend API
	app := os.Getenv("FLY_APP_NAME")
	mid := os.Getenv("FLY_MACHINE_ID")
	url := fmt.Sprintf("http://flaps/v1/apps/%s/machines/%s/suspend", app, mid)

	d := &net.Dialer{}
	tr := &http.Transport{
		DialContext: func(c context.Context, network, addr string) (net.Conn, error) {
			return d.DialContext(c, "unix", "/.fly/api")
		},
	}
	client := &http.Client{Transport: tr}

	req, _ := http.NewRequestWithContext(ctx, http.MethodPost, url, nil)
	resp, err := client.Do(req)
	if err != nil {
		m.logger.Debug("flaps suspend call error", "error", err)
		return
	}
	if resp != nil && resp.Body != nil {
		resp.Body.Close()
	}
}
