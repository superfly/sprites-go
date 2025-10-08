//go:build linux

package system

import (
	"context"
	"encoding/json"
	"fmt"
	"log/slog"
	"time"

	"github.com/superfly/sprite-env/pkg/resources"
	"github.com/superfly/sprite-env/pkg/tap"
)

// ResourceMonitor wraps a MonitorGroup for system cgroups
type ResourceMonitor struct {
	monitorGroup *resources.MonitorGroup
	logger       *slog.Logger
}

// NewResourceMonitor creates cgroup monitors for containers, juicefs, and litestream
// The metricsCallback is called for each metrics emission and should handle forwarding to the appropriate destination
func NewResourceMonitor(ctx context.Context, metricsCallback func(interface{})) (*ResourceMonitor, error) {
	logger := tap.Logger(ctx)

	crm := &ResourceMonitor{
		logger: logger,
	}

	// Create monitor group for system cgroups
	opts := resources.MonitorGroupOptions{
		Interval: 15 * time.Second,
		Cgroups: []struct {
			Path string
			Type string
		}{
			{Path: "/sys/fs/cgroup/containers", Type: "sprite"},
			{Path: "/sys/fs/cgroup/juicefs", Type: "juicefs"},
			{Path: "/sys/fs/cgroup/litestream", Type: "litestream"},
		},
		MetricsCallback: func(metrics interface{}) {
			crm.logMetrics(metrics)
			if metricsCallback != nil {
				metricsCallback(metrics)
			}
		},
	}

	monitorGroup, err := resources.NewMonitorGroup(opts)
	if err != nil {
		return nil, fmt.Errorf("failed to create monitor group: %w", err)
	}
	if monitorGroup == nil {
		return nil, fmt.Errorf("failed to create any resource monitors")
	}

	crm.monitorGroup = monitorGroup

	// Log initial stats for each monitor
	for _, monitor := range monitorGroup.Monitors() {
		if mgr := monitor.GetManager(); mgr != nil {
			stats, err := mgr.ReadStats()
			if err != nil {
				logger.Warn("Failed to read initial cgroup stats", "error", err)
			} else {
				logger.Info("Cgroup resource monitor created",
					"type", monitor.Type(),
					"interval", opts.Interval,
					"initial_memory_mb", stats.MemoryCurrentBytes/1024/1024,
					"initial_cpu_s", stats.CPUUsageTotal.Seconds())
			}
		}
	}

	return crm, nil
}

// logMetrics logs the metrics for debugging
// It accepts any value that can be marshaled to JSON
func (crm *ResourceMonitor) logMetrics(metrics interface{}) {
	// Convert to map for logging
	data, err := json.Marshal(metrics)
	if err != nil {
		crm.logger.Error("Failed to marshal metrics", "error", err)
		return
	}

	var payload map[string]interface{}
	if err := json.Unmarshal(data, &payload); err != nil {
		crm.logger.Error("Failed to unmarshal metrics", "error", err)
		return
	}

	// Log with all fields from the payload
	logArgs := []interface{}{}
	for k, v := range payload {
		logArgs = append(logArgs, k, v)
	}
	crm.logger.Debug("metrics", logArgs...)
}

// Stop stops all monitors
func (crm *ResourceMonitor) Stop() {
	if crm.monitorGroup != nil {
		crm.monitorGroup.Stop()
	}
}

// Flush manually flushes metrics for all monitors
func (crm *ResourceMonitor) Flush() {
	if crm.monitorGroup != nil {
		crm.monitorGroup.Flush()
	}
}

// PreSuspend flushes metrics and pauses the monitoring interval before system suspend
func (crm *ResourceMonitor) PreSuspend() {
	crm.logger.Info("Flushing cgroup metrics and pausing monitoring before suspend")
	if crm.monitorGroup != nil {
		crm.monitorGroup.Flush()
		crm.monitorGroup.Pause()
	}
}

// PostResume resets time tracking, ticks immediately, and resumes monitoring after system resume
func (crm *ResourceMonitor) PostResume() {
	crm.logger.Info("Resetting time tracking and resuming cgroup monitoring after resume")
	if crm.monitorGroup != nil {
		crm.monitorGroup.Resume()
	}
}
