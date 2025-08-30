package main

import (
	"context"
	"fmt"
	"log/slog"
	"net"
	"net/http"
	"os"
	"time"
)

type ActivityMonitor struct {
	logger    *slog.Logger
	system    *System
	idleAfter time.Duration
	eventsCh  chan bool
	stopCh    chan struct{}
	admin     *AdminChannel

	requestCount     int
	totalActiveTime  time.Duration
	busyIntervalFrom time.Time
	lastRequestEnd   time.Time
	isSuspended      bool
}

func NewActivityMonitor(l *slog.Logger, sys *System, idleAfter time.Duration) *ActivityMonitor {
	return &ActivityMonitor{
		logger:    l,
		system:    sys,
		idleAfter: idleAfter,
		eventsCh:  make(chan bool, 64),
		stopCh:    make(chan struct{}),
		admin:     nil,
	}
}

func (m *ActivityMonitor) Start(ctx context.Context) {
	go m.run(ctx)
}

func (m *ActivityMonitor) Observe(active bool) {
	select {
	case m.eventsCh <- active:
	default:
	}
}

func (m *ActivityMonitor) run(ctx context.Context) {
	active := 0
	var idleTimer *time.Timer

	for {
		select {
		case <-ctx.Done():
			return
		case ev := <-m.eventsCh:
			if ev {
				// Request started
				if m.isSuspended {
					m.logger.Info("Resume detected by activity after suspension")
					if m.admin != nil {
						m.admin.SendActivityEvent("resume", map[string]interface{}{
							"suspended_duration_ms": time.Since(m.lastRequestEnd).Milliseconds(),
						})
					}
					m.isSuspended = false
				}

				active++
				if idleTimer != nil {
					idleTimer.Stop()
					idleTimer = nil
				}
			} else {
				// Request ended
				active--
				m.requestCount++
				m.lastRequestEnd = time.Now()

				if active == 0 {
					// No active requests, start idle timer
					idleTimer = time.NewTimer(m.idleAfter)
					go func() {
						<-idleTimer.C
						m.suspend(time.Since(m.lastRequestEnd))
					}()
				}
			}
		}
	}
}

func (m *ActivityMonitor) suspend(inactive time.Duration) {
	m.isSuspended = true
	if m.admin != nil {
		m.admin.SendActivityEvent("suspend", map[string]interface{}{
			"inactive_ms": inactive.Milliseconds(),
			"requests":    m.requestCount,
		})
	}

	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	m.logger.Info("ActivityMonitor: suspending", "requests", m.requestCount, "idle_s", inactive.Seconds())

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
