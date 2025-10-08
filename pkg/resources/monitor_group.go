package resources

import (
	"context"
	"sync"
	"time"
)

// MonitorGroup manages multiple cgroup monitors and handles CPU balance aggregation
type MonitorGroup struct {
	monitors        []*Monitor
	managers        []*Manager
	cancel          context.CancelFunc
	done            chan struct{}
	metricsInterval time.Duration
}

// MonitorGroupOptions configures a monitor group
type MonitorGroupOptions struct {
	// Cgroups to monitor with their metrics types
	Cgroups []struct {
		Path string
		Type string
	}

	// Metrics callback - called for each cgroup's metrics
	MetricsCallback func(interface{})

	// How often to emit metrics
	Interval time.Duration
}

// NewMonitorGroup creates a group of monitors for multiple cgroups and handles
// CPU balance aggregation internally
func NewMonitorGroup(opts MonitorGroupOptions) (*MonitorGroup, error) {
	if opts.Interval == 0 {
		opts.Interval = 15 * time.Second
	}

	mg := &MonitorGroup{
		done:            make(chan struct{}),
		metricsInterval: opts.Interval,
	}

	// Create monitors for each cgroup
	for _, cg := range opts.Cgroups {
		monitorOpts := MonitorOptions{
			Interval:        opts.Interval,
			Type:            cg.Type,
			MetricsCallback: opts.MetricsCallback,
		}

		monitor, err := NewMonitor(cg.Path, monitorOpts)
		if err != nil {
			// Non-fatal - continue with other cgroups
			continue
		}

		mgr := monitor.GetManager()
		if mgr == nil {
			continue
		}

		// Disable individual CPU balance updates - we'll aggregate them
		mgr.SetSkipGlobalCPUBalance(true)

		mg.monitors = append(mg.monitors, monitor)
		mg.managers = append(mg.managers, mgr)
	}

	// Even if no monitors were created, return a valid (empty) MonitorGroup
	// This allows callers to safely call methods on it without nil checks
	
	// Start CPU balance aggregation goroutine only if we have monitors
	if len(mg.monitors) > 0 {
		ctx, cancel := context.WithCancel(context.Background())
		mg.cancel = cancel
		go mg.runCPUBalanceAggregation(ctx)
	} else {
		// No monitors, but still return a valid empty group
		// Close the done channel immediately since there's nothing to monitor
		close(mg.done)
	}

	return mg, nil
}

// runCPUBalanceAggregation aggregates CPU usage from all managers and updates
// the global CPU balance singleton
func (mg *MonitorGroup) runCPUBalanceAggregation(ctx context.Context) {
	defer close(mg.done)

	ticker := time.NewTicker(mg.metricsInterval)
	defer ticker.Stop()

	for {
		select {
		case <-ctx.Done():
			return
		case now := <-ticker.C:
			mg.tickCPUBalance(now)
		}
	}
}

// tickCPUBalance aggregates CPU usage from all managers and updates the global balance
func (mg *MonitorGroup) tickCPUBalance(now time.Time) {
	var totalCPUUsage time.Duration
	for _, mgr := range mg.managers {
		stats, err := mgr.ReadStats()
		if err != nil {
			continue
		}
		totalCPUUsage += stats.CPUUsageTotal
	}

	// Update global CPU balance with aggregated usage
	GetCPUBalance().Tick(now, totalCPUUsage)
}

// Stop stops all monitors and the CPU balance aggregation
func (mg *MonitorGroup) Stop() {
	if mg.cancel != nil {
		mg.cancel()
	}
	<-mg.done

	// Stop all monitors
	var wg sync.WaitGroup
	for _, mon := range mg.monitors {
		wg.Add(1)
		go func(m *Monitor) {
			defer wg.Done()
			m.Stop()
		}(mon)
	}
	wg.Wait()
}

// Flush flushes all monitors and triggers a CPU balance update
func (mg *MonitorGroup) Flush() {
	for _, mon := range mg.monitors {
		mon.Flush()
	}
	mg.tickCPUBalance(time.Now())
}

// Pause pauses all monitors
func (mg *MonitorGroup) Pause() {
	for _, mon := range mg.monitors {
		mon.Pause()
	}
}

// Resume resumes all monitors and resets time tracking
func (mg *MonitorGroup) Resume() {
	// Reset time tracking for all managers
	for _, mgr := range mg.managers {
		mgr.ResetTimeTracking()
	}

	// Reset global CPU balance time tracking
	GetCPUBalance().ResetTimeTracking()

	// Resume all monitors
	for _, mon := range mg.monitors {
		mon.Resume()
	}
}

// Monitors returns the underlying monitors for direct access if needed
func (mg *MonitorGroup) Monitors() []*Monitor {
	return mg.monitors
}
