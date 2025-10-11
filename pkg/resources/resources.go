package resources

import (
	"errors"
	"log/slog"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"sync/atomic"
	"time"
)

// Manager manages cgroup v2 resource limits and usage for a single cgroup path.
// It only reads/writes files inside the provided cgroupPath.
type Manager struct {
	cgroupPath string

	// Last CPU usage for this cgroup
	lastCPUUsage atomic.Int64 // last observed cpu usage in nanoseconds
	lastSampleNS atomic.Int64 // last sample wall time (Unix nano)

	// memory integral
	memoryGBSeconds atomic.Pointer[float64] // accumulated GB-seconds

	// IO integrals
	ioReadGB   atomic.Pointer[float64] // accumulated read gigabytes
	ioWriteGB  atomic.Pointer[float64] // accumulated write gigabytes
	ioReadOps  atomic.Int64            // accumulated read operations
	ioWriteOps atomic.Int64            // accumulated write operations

	// Last observed IO values for delta calculation
	lastIOReadBytes  atomic.Uint64
	lastIOWriteBytes atomic.Uint64
	lastIOReadOps    atomic.Uint64
	lastIOWriteOps   atomic.Uint64

	// Timeseries for metrics (used for trend analysis)
	cpuThrottlePct     *Series // CPU throttle percentage over time
	memoryUsagePct     *Series // Memory usage percentage over time
	memoryUsageBytes   *Series // Memory usage in bytes over time
	memoryStallTotal   *Series // Memory stall microseconds total (monotonic counter)
	workingsetRefaults *Series // Workingset refault rate (monotonic)
	pageMajorFaults    *Series // Major page fault rate (monotonic)
	ioReadBytesTotal   *Series // IO read bytes total (monotonic counter)
	ioWriteBytesTotal  *Series // IO write bytes total (monotonic counter)
	ioReadOpsTotal     *Series // IO read operations total (monotonic counter)
	ioWriteOpsTotal    *Series // IO write operations total (monotonic counter)

	// skipGlobalCPUBalance disables updating the global CPU balance singleton.
	// Set this to true when using multiple managers to aggregate CPU usage externally.
	skipGlobalCPUBalance bool
}

// NewManager creates a Manager for the given cgroup path.
func NewManager(cgroupPath string) (*Manager, error) {
	if cgroupPath == "" {
		return nil, errors.New("cgroupPath required")
	}

	m := &Manager{
		cgroupPath: cgroupPath,
		// Initialize timeseries (keep 100 samples, ~10 minutes at 5-6 second intervals)
		cpuThrottlePct:     NewGaugeSeries(100),
		memoryUsagePct:     NewGaugeSeries(100),
		memoryUsageBytes:   NewGaugeSeries(100),
		memoryStallTotal:   NewCounterSeries(100),
		workingsetRefaults: NewCounterSeries(100),
		pageMajorFaults:    NewCounterSeries(100),
		ioReadBytesTotal:   NewCounterSeries(100),
		ioWriteBytesTotal:  NewCounterSeries(100),
		ioReadOpsTotal:     NewCounterSeries(100),
		ioWriteOpsTotal:    NewCounterSeries(100),
	}
	var zero float64
	m.memoryGBSeconds.Store(&zero)
	m.ioReadGB.Store(&zero)
	m.ioWriteGB.Store(&zero)
	// Initialize last CPU usage to current to avoid a large first delta
	now := time.Now()
	st, _ := m.ReadCPUStat()
	m.lastCPUUsage.Store(st.UsageTotal.Nanoseconds())
	m.lastSampleNS.Store(now.UnixNano())

	// Initialize global CPU balance only if this manager will update it (skipGlobalCPUBalance=false)
	// and the global balance hasn't been initialized yet (lastCPUUsage=0).
	// This prevents each new manager from overwriting the global state when multiple managers exist.
	// For MonitorGroup usage, skipGlobalCPUBalance is set to true before any ticks occur.
	if !m.skipGlobalCPUBalance {
		cb := GetCPUBalance()
		// Only initialize if not already set (atomic compare-and-swap would be ideal, but this is close enough)
		if cb.lastCPUUsage.Load() == 0 {
			cb.lastCPUUsage.Store(st.UsageTotal.Nanoseconds())
			cb.lastSampleNS.Store(now.UnixNano())
		}
	}

	return m, nil
}

// ReadStats reads current usage stats from cgroup files.
func (m *Manager) ReadStats() (Stats, error) {
	cpu, err := m.ReadCPUStat()
	if err != nil {
		return Stats{}, err
	}
	memCurrent, err := m.readUintFromFile("memory.current")
	if err != nil {
		// Suppress noisy warning in environments without cgroup memory controller
		memCurrent = 0
	}
	ioStats, _ := m.readIOStat()

	s := Stats{
		CPUUsageTotal:      cpu.UsageTotal,
		MemoryCurrentBytes: memCurrent,
		IOReadBytes:        ioStats.ReadBytes,
		IOWriteBytes:       ioStats.WriteBytes,
		CPUDeficit:         time.Duration(0), // CPU deficit is now tracked globally
	}
	if p := m.memoryGBSeconds.Load(); p != nil {
		s.MemoryGBSeconds = *p
	}
	if p := m.ioReadGB.Load(); p != nil {
		s.IOReadGB = *p
	}
	if p := m.ioWriteGB.Load(); p != nil {
		s.IOWriteGB = *p
	}
	s.IOReadOps = uint64(m.ioReadOps.Load())
	s.IOWriteOps = uint64(m.ioWriteOps.Load())
	return s, nil
}

// Tick samples current usage and updates trackers for CPU banking and memory GB-seconds.
// Also records samples to timeseries for trend analysis.
func (m *Manager) Tick(now time.Time) error {
	// Calculate elapsed time since last tick
	lastWallNS := m.lastSampleNS.Load()
	elapsed := time.Duration(now.UnixNano() - lastWallNS)
	if elapsed < 0 {
		elapsed = 0
	}

	// Update CPU metrics
	m.tickCPU(now, elapsed)

	// Update memory metrics
	m.tickMemory(now, elapsed)

	// Update IO metrics
	m.tickIO(now)

	// Update last sample time
	m.lastSampleNS.Store(now.UnixNano())
	return nil
}

// ResetTimeTracking resets the time tracking to the current moment.
// This should be called after suspend/resume to prevent crediting CPU time
// for the period when the system was suspended.
func (m *Manager) ResetTimeTracking() {
	now := time.Now()
	m.lastSampleNS.Store(now.UnixNano())
}

// CheckPressure analyzes current resource usage and returns pressure indicators.
// It uses timeseries data to predict future resource needs and detect trends.
// For memory pressure, it also estimates the optimal memory size based on:
// - Predicted memory allocation stall percentages
// - Workingset refault rate trends
// - OOM events and page fault rate trends
// The EstimatedOptimalMemoryMB field provides a recommendation for scaling.
func (m *Manager) CheckPressure() (ResourcePressure, error) {
	var p ResourcePressure
	logger := slog.Default().With("cgroup", filepath.Base(m.cgroupPath))

	// Check CPU pressure
	if err := m.checkCPUPressure(&p, logger); err != nil {
		return p, err
	}

	// Check memory pressure
	if err := m.checkMemoryPressure(&p, logger); err != nil {
		return p, err
	}

	return p, nil
}

// Helpers

// readFile reads a file from the cgroup directory
func (m *Manager) readFile(name string) ([]byte, error) {
	return os.ReadFile(filepath.Join(m.cgroupPath, name))
}

// readUintFromFile reads a uint64 from a cgroup file
func (m *Manager) readUintFromFile(name string) (uint64, error) {
	b, err := os.ReadFile(filepath.Join(m.cgroupPath, name))
	if err != nil {
		return 0, err
	}
	s := strings.TrimSpace(string(b))
	// memory.high and memory.max can be "max"
	if s == "max" {
		return ^uint64(0), nil
	}
	v, err := strconv.ParseUint(s, 10, 64)
	if err != nil {
		return 0, err
	}
	return v, nil
}

// writeFile writes content to a cgroup file
func (m *Manager) writeFile(name string, content string) error {
	p := filepath.Join(m.cgroupPath, name)
	return os.WriteFile(p, []byte(content), 0o644)
}

// readPressureFile reads and parses a cgroup v2 pressure file (cpu.pressure, memory.pressure, io.pressure)
func (m *Manager) readPressureFile(name string) (PressureStall, error) {
	b, err := os.ReadFile(filepath.Join(m.cgroupPath, name))
	if err != nil {
		return PressureStall{}, err
	}

	var ps PressureStall
	for _, line := range strings.Split(string(b), "\n") {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}

		// Parse lines like: "some avg10=0.00 avg60=0.00 avg300=0.00 total=12345"
		parts := strings.Fields(line)
		if len(parts) < 5 {
			continue
		}

		var target *struct {
			Avg10  float64
			Avg60  float64
			Avg300 float64
			Total  uint64
		}

		switch parts[0] {
		case "some":
			target = &ps.Some
		case "full":
			target = &ps.Full
		default:
			continue
		}

		for _, part := range parts[1:] {
			key, val, ok := strings.Cut(part, "=")
			if !ok {
				continue
			}

			switch key {
			case "avg10":
				target.Avg10, _ = strconv.ParseFloat(val, 64)
			case "avg60":
				target.Avg60, _ = strconv.ParseFloat(val, 64)
			case "avg300":
				target.Avg300, _ = strconv.ParseFloat(val, 64)
			case "total":
				target.Total = parseUint(val)
			}
		}
	}

	return ps, nil
}

// parseUint parses a string as uint64, returning 0 on error
func parseUint(s string) uint64 {
	v, _ := strconv.ParseUint(strings.TrimSpace(s), 10, 64)
	return v
}

// formatUS formats a duration as microseconds string
func formatUS(d time.Duration) string {
	if d <= 0 {
		// Kernel defaults to 100000 (100ms) period if omitted; we require explicit.
		return "100000"
	}
	return strconv.FormatInt(d.Microseconds(), 10)
}

// CPUBankBalance returns the global VM-level CPU bank balance.
// This is a convenience method that delegates to the global CPU balance singleton.
func (m *Manager) CPUBankBalance() time.Duration {
	return GetCPUBalance().Balance()
}

// CPUDeficit returns the global VM-level CPU deficit.
// This is a convenience method that delegates to the global CPU balance singleton.
func (m *Manager) CPUDeficit() time.Duration {
	return GetCPUBalance().Deficit()
}

// SetSkipGlobalCPUBalance sets whether this manager should skip updating the global CPU balance.
// This should be set to true when multiple managers are aggregating CPU usage externally.
func (m *Manager) SetSkipGlobalCPUBalance(skip bool) {
	m.skipGlobalCPUBalance = skip
}
