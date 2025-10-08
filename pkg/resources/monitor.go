package resources

import (
	"context"
	"encoding/json"
	"sync"
	"time"
)

// ResourceManager is the interface that Monitor uses to interact with cgroups
type ResourceManager interface {
	Tick(now time.Time) error
	ReadStats() (Stats, error)
	CPUBankBalance() time.Duration
	CPUDeficit() time.Duration
}

// MonitorOptions configures the resource monitor
type MonitorOptions struct {
	// Metrics callback - called on every interval for all metrics (cgroup and VM-level)
	MetricsCallback func(interface{})

	// How often to emit metrics
	Interval time.Duration

	// Type identifies the metrics source (e.g., "sprite")
	Type string
}

// Metrics contains accumulated resource usage for a cgroup
type Metrics struct {
	// Type identifies the metrics source (e.g., "sprite")
	Type string `json:"type"`

	// Monotonic counters (delta since last flush)
	CPUSeconds    float64 `json:"cpu_s"`
	MemorySeconds float64 `json:"memory_s"`      // memory GB-seconds
	CPUDeficit    float64 `json:"cpu_deficit_s"` // accumulated CPU deficit
	IOReadGB      float64 `json:"io_read_gb"`    // read gigabytes
	IOWriteGB     float64 `json:"io_write_gb"`   // write gigabytes
	IOPSRead      uint64  `json:"iops_read"`     // read operations
	IOPSWrite     uint64  `json:"iops_write"`    // write operations

	// Monotonic counters (cumulative totals)
	CPUSecondsTotal    float64 `json:"cpu_s_total"`
	RuntimeSeconds     float64 `json:"runtime_s"`           // wall clock time (monotonic, excluding suspended time)
	MemorySecondsTotal float64 `json:"memory_s_total"`      // memory GB-seconds
	CPUDeficitTotal    float64 `json:"cpu_deficit_s_total"` // accumulated CPU deficit
	IOReadGBTotal      float64 `json:"io_read_gb_total"`    // read gigabytes
	IOWriteGBTotal     float64 `json:"io_write_gb_total"`   // write gigabytes
	IOPSReadTotal      uint64  `json:"iops_read_total"`     // read operations
	IOPSWriteTotal     uint64  `json:"iops_write_total"`    // write operations

	// Current state
	MemoryCurrentMB uint64 `json:"memory_current_mb"`
}

// VMMetrics contains VM-level CPU balance information
type VMMetrics struct {
	// Type is always "vm" for VM metrics
	Type string `json:"type"`

	// CPU balance tracking
	CPUBalance      float64 `json:"cpu_balance_s"`       // Current CPU bank balance in seconds
	CPUDeficitTotal float64 `json:"cpu_deficit_s_total"` // Accumulated CPU deficit in seconds
}

// MarshalJSON implements json.Marshaler
func (m Metrics) MarshalJSON() ([]byte, error) {
	// Already uses json tags with underscore case
	type Alias Metrics
	return json.Marshal((Alias)(m))
}

// Monitor manages a cgroup with metrics emission (accounting only, no limit setting)
type Monitor struct {
	manager ResourceManager
	opts    MonitorOptions

	// Accumulated counters (reset on flush for deltas)
	mu                sync.Mutex
	cpuSecondsUsed    float64
	memoryGBSeconds   float64
	cpuDeficitSeconds float64
	ioReadGB          float64
	ioWriteGB         float64
	ioReadOps         uint64
	ioWriteOps        uint64

	// Cumulative totals (never reset)
	cpuSecondsTotal  float64
	runtimeSeconds   float64 // monotonic runtime (excluding suspended time)
	memoryGBSTotal   float64
	cpuDeficitTotal  float64
	ioReadGBTotal    float64
	ioWriteGBTotal   float64
	ioReadOpsTotal   uint64
	ioWriteOpsTotal  uint64
	lastRuntimeCheck time.Time

	// Last known values for delta calculation
	lastCPUUsage   time.Duration
	lastMemoryGBS  float64
	lastCPUDeficit time.Duration
	lastIOReadGB   float64
	lastIOWriteGB  float64
	lastIOReadOps  uint64
	lastIOWriteOps uint64

	// Ticker for interval control
	ticker *time.Ticker
	mu2    sync.Mutex // Protects ticker

	cancel   context.CancelFunc
	done     chan struct{}
	pauseCh  chan struct{}
	resumeCh chan struct{}

	// Global VM metrics tracking
	shouldEmitVMMetrics bool // Whether this monitor emits VM-level metrics
}

// NewMonitor creates and starts a resource monitor with a real Manager
func NewMonitor(cgroupPath string, opts MonitorOptions) (*Monitor, error) {
	manager, err := NewManager(cgroupPath)
	if err != nil {
		return nil, err
	}
	return NewMonitorWithManager(manager, opts), nil
}

var (
	vmMetricsMonitor     *Monitor
	vmMetricsMonitorLock sync.Mutex
)

// NewMonitorWithManager creates and starts a resource monitor with a provided manager
func NewMonitorWithManager(manager ResourceManager, opts MonitorOptions) *Monitor {
	// Set defaults
	if opts.Interval == 0 {
		opts.Interval = 15 * time.Second
	}
	if opts.Type == "" {
		opts.Type = "cgroup"
	}

	mon := &Monitor{
		manager:          manager,
		opts:             opts,
		done:             make(chan struct{}),
		pauseCh:          make(chan struct{}),
		resumeCh:         make(chan struct{}),
		lastRuntimeCheck: time.Now(),
	}

	// First monitor created becomes the VM metrics emitter
	vmMetricsMonitorLock.Lock()
	if vmMetricsMonitor == nil {
		vmMetricsMonitor = mon
		mon.shouldEmitVMMetrics = true
	}
	vmMetricsMonitorLock.Unlock()

	// Start monitoring loop
	ctx, cancel := context.WithCancel(context.Background())
	mon.cancel = cancel
	go mon.run(ctx)

	return mon
}

// run is the main monitoring loop
func (mon *Monitor) run(ctx context.Context) {
	defer close(mon.done)

	mon.mu2.Lock()
	mon.ticker = time.NewTicker(mon.opts.Interval)
	ticker := mon.ticker
	mon.mu2.Unlock()
	defer ticker.Stop()

	paused := false

	for {
		select {
		case <-ctx.Done():
			return

		case <-mon.pauseCh:
			if !paused {
				ticker.Stop()
				paused = true
				// Stop runtime tracking
				mon.mu.Lock()
				mon.lastRuntimeCheck = time.Time{}
				mon.mu.Unlock()
			}

		case <-mon.resumeCh:
			if paused {
				ticker.Reset(mon.opts.Interval)
				paused = false
				// Restart runtime tracking
				mon.mu.Lock()
				mon.lastRuntimeCheck = time.Now()
				mon.mu.Unlock()
			}

		case now := <-ticker.C:
			if !paused {
				// Tick the manager to update timeseries
				mon.manager.Tick(now)
				// Emit metrics every tick
				mon.emitMetrics()
				// Emit VM-level CPU balance metrics (only from first monitor)
				if mon.shouldEmitVMMetrics {
					mon.emitVMMetrics()
				}
			}
		}
	}
}

// emitMetrics calculates and emits accumulated metrics, then resets delta counters
func (mon *Monitor) emitMetrics() {
	mon.mu.Lock()
	defer mon.mu.Unlock()

	// Get current stats
	stats, err := mon.manager.ReadStats()
	if err != nil {
		return
	}

	// Calculate runtime delta (wall clock time, excluding suspended periods)
	now := time.Now()
	if !mon.lastRuntimeCheck.IsZero() {
		runtimeDelta := now.Sub(mon.lastRuntimeCheck).Seconds()
		mon.runtimeSeconds += runtimeDelta
	}
	mon.lastRuntimeCheck = now

	// Calculate deltas since last sample
	cpuDelta := stats.CPUUsageTotal - mon.lastCPUUsage
	memoryGBSDelta := stats.MemoryGBSeconds - mon.lastMemoryGBS
	cpuDeficitDelta := stats.CPUDeficit - mon.lastCPUDeficit
	ioReadGBDelta := stats.IOReadGB - mon.lastIOReadGB
	ioWriteGBDelta := stats.IOWriteGB - mon.lastIOWriteGB
	ioReadOpsDelta := stats.IOReadOps - mon.lastIOReadOps
	ioWriteOpsDelta := stats.IOWriteOps - mon.lastIOWriteOps

	// Accumulate deltas (reset on flush)
	mon.cpuSecondsUsed += cpuDelta.Seconds()
	mon.memoryGBSeconds += memoryGBSDelta
	mon.cpuDeficitSeconds += cpuDeficitDelta.Seconds()
	mon.ioReadGB += ioReadGBDelta
	mon.ioWriteGB += ioWriteGBDelta
	mon.ioReadOps += ioReadOpsDelta
	mon.ioWriteOps += ioWriteOpsDelta

	// Accumulate totals (never reset)
	mon.cpuSecondsTotal += cpuDelta.Seconds()
	mon.memoryGBSTotal += memoryGBSDelta
	mon.cpuDeficitTotal += cpuDeficitDelta.Seconds()
	mon.ioReadGBTotal += ioReadGBDelta
	mon.ioWriteGBTotal += ioWriteGBDelta
	mon.ioReadOpsTotal += ioReadOpsDelta
	mon.ioWriteOpsTotal += ioWriteOpsDelta

	// Build metrics
	metrics := Metrics{
		Type: mon.opts.Type,

		// Deltas since last flush
		CPUSeconds:    mon.cpuSecondsUsed,
		MemorySeconds: mon.memoryGBSeconds,
		CPUDeficit:    mon.cpuDeficitSeconds,
		IOReadGB:      mon.ioReadGB,
		IOWriteGB:     mon.ioWriteGB,
		IOPSRead:      mon.ioReadOps,
		IOPSWrite:     mon.ioWriteOps,

		// Cumulative totals
		CPUSecondsTotal:    mon.cpuSecondsTotal,
		RuntimeSeconds:     mon.runtimeSeconds,
		MemorySecondsTotal: mon.memoryGBSTotal,
		CPUDeficitTotal:    mon.cpuDeficitTotal,
		IOReadGBTotal:      mon.ioReadGBTotal,
		IOWriteGBTotal:     mon.ioWriteGBTotal,
		IOPSReadTotal:      mon.ioReadOpsTotal,
		IOPSWriteTotal:     mon.ioWriteOpsTotal,

		// Current state
		MemoryCurrentMB: stats.MemoryCurrentBytes / 1024 / 1024,
	}

	// Emit via callback
	if mon.opts.MetricsCallback != nil {
		mon.opts.MetricsCallback(metrics)
	}

	// Reset delta counters (totals are never reset)
	mon.cpuSecondsUsed = 0
	mon.memoryGBSeconds = 0
	mon.cpuDeficitSeconds = 0
	mon.ioReadGB = 0
	mon.ioWriteGB = 0
	mon.ioReadOps = 0
	mon.ioWriteOps = 0

	// Update last known values
	mon.lastCPUUsage = stats.CPUUsageTotal
	mon.lastMemoryGBS = stats.MemoryGBSeconds
	mon.lastCPUDeficit = stats.CPUDeficit
	mon.lastIOReadGB = stats.IOReadGB
	mon.lastIOWriteGB = stats.IOWriteGB
	mon.lastIOReadOps = stats.IOReadOps
	mon.lastIOWriteOps = stats.IOWriteOps
}

// Flush manually ticks the manager, emits fresh metrics, and resets the interval
func (mon *Monitor) Flush() {
	// Tick to get fresh data
	mon.manager.Tick(time.Now())

	// Emit metrics
	mon.emitMetrics()

	// Reset the ticker interval
	mon.mu2.Lock()
	if mon.ticker != nil {
		mon.ticker.Reset(mon.opts.Interval)
	}
	mon.mu2.Unlock()
}

// Pause stops the monitoring interval (for suspend)
func (mon *Monitor) Pause() {
	select {
	case mon.pauseCh <- struct{}{}:
	default:
		// Already paused or channel full
	}
}

// Resume resumes the monitoring interval and flushes immediately (for resume after suspend)
func (mon *Monitor) Resume() {
	// Flush to capture current state and reset interval
	mon.Flush()

	// Resume the interval
	select {
	case mon.resumeCh <- struct{}{}:
	default:
		// Already running or channel full
	}
}

// Stop stops the monitor and waits for it to finish
func (mon *Monitor) Stop() {
	if mon.cancel != nil {
		mon.cancel()
	}
	<-mon.done
}

// Manager returns the underlying resource manager for direct access
func (mon *Monitor) Manager() ResourceManager {
	return mon.manager
}

// GetManager returns the underlying manager as a *Manager if it is one, nil otherwise
func (mon *Monitor) GetManager() *Manager {
	if mgr, ok := mon.manager.(*Manager); ok {
		return mgr
	}
	return nil
}

// Type returns the type identifier for this monitor
func (mon *Monitor) Type() string {
	return mon.opts.Type
}

// emitVMMetrics emits VM-level CPU balance metrics.
// This is called only by the first monitor created to avoid duplicate metrics.
// Note: The global CPU balance is already updated by Manager.tickCPU, so we just read it here.
func (mon *Monitor) emitVMMetrics() {
	if mon.opts.MetricsCallback == nil {
		return
	}

	// Get CPU balance from global singleton
	cb := GetCPUBalance()

	// Build VM metrics
	vmMetrics := VMMetrics{
		Type:            "vm",
		CPUBalance:      cb.Balance().Seconds(),
		CPUDeficitTotal: cb.Deficit().Seconds(),
	}

	// Emit via callback
	mon.opts.MetricsCallback(vmMetrics)
}
