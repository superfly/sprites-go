package resources

import (
	"bufio"
	"fmt"
	"log/slog"
	"math"
	"os"
	"path/filepath"
	"strings"
	"time"
)

// SetMinimumMemory sets memory.low, indicating protected memory that is less likely to be reclaimed.
func (m *Manager) SetMinimumMemory(bytes uint64) error {
	return m.writeFile("memory.low", fmt.Sprintf("%d\n", bytes))
}

// SetMaximumMemory sets memory.high (soft limit with throttling). Pass 0 to set "max" (no limit).
func (m *Manager) SetMaximumMemory(bytes uint64) error {
	if bytes == 0 {
		return m.writeFile("memory.high", "max\n")
	}
	return m.writeFile("memory.high", fmt.Sprintf("%d\n", bytes))
}

// readMemoryStat reads and parses memory.stat file
func (m *Manager) readMemoryStat() (MemoryStat, error) {
	f, err := os.Open(filepath.Join(m.cgroupPath, "memory.stat"))
	if err != nil {
		return MemoryStat{}, err
	}
	defer f.Close()

	var stat MemoryStat
	scanner := bufio.NewScanner(f)
	for scanner.Scan() {
		line := scanner.Text()
		key, val, ok := strings.Cut(line, " ")
		if !ok {
			continue
		}

		v := parseUint(val)
		switch key {
		case "anon":
			stat.Anon = v
		case "file":
			stat.File = v
		case "kernel_stack":
			stat.KernelStack = v
		case "slab":
			stat.Slab = v
		case "sock":
			stat.Sock = v
		case "shmem":
			stat.Shmem = v
		case "file_mapped":
			stat.FileMapped = v
		case "file_dirty":
			stat.FileDirty = v
		case "file_writeback":
			stat.FileWriteback = v
		case "pgfault":
			stat.Pgfault = v
		case "pgmajfault":
			stat.Pgmajfault = v
		case "workingset_refault":
			stat.WorkingsetRefault = v
		case "workingset_activate":
			stat.WorkingsetActivate = v
		case "workingset_nodereclaim":
			stat.WorkingsetNodereclaim = v
		case "pgrefill":
			stat.Pgrefill = v
		case "pgscan":
			stat.Pgscan = v
		case "pgsteal":
			stat.Pgsteal = v
		case "pgactivate":
			stat.Pgactivate = v
		case "pgdeactivate":
			stat.Pgdeactivate = v
		}
	}

	return stat, scanner.Err()
}

// readMemoryEvents reads and parses memory.events file
func (m *Manager) readMemoryEvents() (map[string]uint64, error) {
	b, err := os.ReadFile(filepath.Join(m.cgroupPath, "memory.events"))
	if err != nil {
		return nil, err
	}

	events := make(map[string]uint64)
	for _, line := range strings.Split(string(b), "\n") {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}

		key, val, ok := strings.Cut(line, " ")
		if ok {
			events[key] = parseUint(val)
		}
	}

	return events, nil
}

// PredictMemoryBytes is no longer supported - predictions removed
func (m *Manager) PredictMemoryBytes(t time.Time) (bytes uint64, confidence float64, ok bool) {
	return 0, 0, false
}

// tickMemory updates memory GB-seconds integral and timeseries.
func (m *Manager) tickMemory(now time.Time, elapsed time.Duration) {
	memCurrent, err := m.readUintFromFile("memory.current")
	if err != nil {
		// Suppress noisy warning in environments without cgroup memory controller
		memCurrent = 0
	}
	memHigh, _ := m.readUintFromFile("memory.high")

	// Memory GB-seconds integral
	if elapsed > 0 {
		added := (float64(memCurrent) / 1_000_000_000.0) * elapsed.Seconds()
		for {
			p := m.memoryGBSeconds.Load()
			if p == nil {
				var zero float64
				if m.memoryGBSeconds.CompareAndSwap(nil, &zero) {
					continue
				}
				continue
			}
			// Recompute newVal on each iteration to ensure correctness
			newVal := *p + added
			// Store by replacing pointer to avoid races without locks
			nv := new(float64)
			*nv = newVal
			if m.memoryGBSeconds.CompareAndSwap(p, nv) {
				break
			}
			// On CAS failure, p is now stale, loop will reload and recompute
		}
	}

	// Record memory usage
	m.memoryUsageBytes.Add(now, float64(memCurrent))
	if memHigh > 0 && memHigh != ^uint64(0) {
		memUsagePct := float64(memCurrent) / float64(memHigh) * 100
		m.memoryUsagePct.Add(now, memUsagePct)
	}

	// Record memory pressure (total stall microseconds as monotonic counter)
	if memPressure, err := m.readPressureFile("memory.pressure"); err == nil {
		m.memoryStallTotal.Add(now, float64(memPressure.Some.Total))
	}

	// Record memory.stat counters (monotonic)
	if memStat, err := m.readMemoryStat(); err == nil {
		m.workingsetRefaults.Add(now, float64(memStat.WorkingsetRefault))
		m.pageMajorFaults.Add(now, float64(memStat.Pgmajfault))
	}
}

// checkMemoryPressure analyzes memory pressure and updates the ResourcePressure struct.
func (m *Manager) checkMemoryPressure(p *ResourcePressure, logger *slog.Logger) error {
	memCurrent, err := m.readUintFromFile("memory.current")
	if err != nil {
		// Suppress noisy warning in environments without cgroup memory controller
		memCurrent = 0
	}
	memHigh, _ := m.readUintFromFile("memory.high")

	if memHigh > 0 && memHigh != ^uint64(0) {
		p.MemoryUsagePercent = float64(memCurrent) / float64(memHigh) * 100

		// Check current usage for upgrade needs
		if p.MemoryUsagePercent > 90 {
			p.MemoryPressure = true
			p.NeedsMemoryUpgrade = true
		}
	}

	// Track factors for estimating optimal memory
	var memoryPressureFactors []float64

	// Check memory.pressure for actual stall information and predict trends
	// Using the total counter to calculate stall rate (microseconds/second)
	if memPressure, err := m.readPressureFile("memory.pressure"); err == nil {
		// Get current stall rate from timeseries (microseconds of stall per second)
		// A rate of 10,000 us/s = 1% stall time (10ms per second)
		currentStallRate := 0.0
		if delta, elapsed, ok := m.memoryStallTotal.Increase(); ok && elapsed > 0 {
			// Calculate rate: microseconds of stall per second
			currentStallRate = delta / elapsed.Seconds()
		}

		// Calculate current stall percentage from rate
		currentStallPct := currentStallRate / 10000.0 // Convert us/s to percentage

		// Detect pressure if stall rate > 5% (50,000 us/s)
		if currentStallPct > 5 {
			p.MemoryPressure = true
			logger.Warn("Memory allocation stalls detected",
				"cgroup", filepath.Base(m.cgroupPath),
				"stall_rate_us_per_s", fmt.Sprintf("%.0f", currentStallRate),
				"stall_percent", fmt.Sprintf("%.1f%%", currentStallPct),
				"usage_percent", fmt.Sprintf("%.1f%%", p.MemoryUsagePercent))

			// Estimate based on stall percentage
			memoryPressureFactors = append(memoryPressureFactors, 1.0+currentStallPct/100)
		}

		// Need upgrade if sustained high memory stalls
		// Avg60 > 10% or Full.Avg10 > 5% or current rate > 15% (150,000 us/s)
		if memPressure.Some.Avg60 > 10 || memPressure.Full.Avg10 > 5 || currentStallPct > 15 {
			p.NeedsMemoryUpgrade = true
			logger.Error("High memory allocation stalls - upgrade needed",
				"cgroup", filepath.Base(m.cgroupPath),
				"stall_some_60s", fmt.Sprintf("%.1f%%", memPressure.Some.Avg60),
				"stall_full_10s", fmt.Sprintf("%.1f%%", memPressure.Full.Avg10),
				"current_rate_us_per_s", fmt.Sprintf("%.0f", currentStallRate),
				"current_pct", fmt.Sprintf("%.1f%%", currentStallPct))

			// Use the higher of sustained or current stalls for estimation
			factor := 1.0 + math.Max(math.Max(memPressure.Some.Avg60, memPressure.Full.Avg10*2), currentStallPct)/100
			memoryPressureFactors = append(memoryPressureFactors, factor)
		}
	}

	// Read memory.stat for additional pressure signals
	memStat, err := m.readMemoryStat()
	if err == nil {
		// High page fault rate indicates memory pressure
		p.MemoryReclaims = memStat.Pgrefill + memStat.Pgsteal

		// Workingset refaults indicate we're thrashing
		if memStat.WorkingsetRefault > 1000 {
			p.MemoryPressure = true
			logger.Warn("Memory thrashing detected - working set doesn't fit",
				"workingset_refaults", memStat.WorkingsetRefault,
				"workingset_activations", memStat.WorkingsetActivate,
				"usage_percent", fmt.Sprintf("%.1f%%", p.MemoryUsagePercent))
			p.NeedsMemoryUpgrade = true

			// If we have many refaults, estimate we need more memory proportional to refault rate
			// A high refault:activation ratio suggests significant memory shortage
			if memStat.WorkingsetActivate > 0 {
				refaultRatio := float64(memStat.WorkingsetRefault) / float64(memStat.WorkingsetActivate)
				// If refaults > activations, we need at least 2x memory
				memoryPressureFactors = append(memoryPressureFactors, 1.0+math.Min(refaultRatio, 2.0))
			}
		}

		// Major faults mean we're swapping (very bad)
		if memStat.Pgmajfault > 100 {
			p.NeedsMemoryUpgrade = true
			logger.Error("Major page faults - severe memory pressure",
				"major_faults", memStat.Pgmajfault,
				"page_reclaims", p.MemoryReclaims)
		}
	}

	// Also check memory.events for OOM kills
	if events, err := m.readMemoryEvents(); err == nil {
		if events["oom_kill"] > 0 {
			p.MemoryPressure = true
			p.NeedsMemoryUpgrade = true
			logger.Error("OOM killer activated",
				"oom_kills", events["oom_kill"],
				"memory_high_hits", events["high"])
		}
		// High number of memory.high events means we're hitting soft limit frequently
		if events["high"] > 100 {
			p.MemoryPressure = true
			p.NeedsMemoryUpgrade = true
			logger.Warn("Hitting memory.high limit frequently - throttling occurring",
				"high_events", events["high"])
		}
	}

	// Additional check: if current usage is at or above memory.high, system is being throttled
	if memHigh > 0 && memHigh != ^uint64(0) && memCurrent >= memHigh {
		p.MemoryPressure = true
		p.NeedsMemoryUpgrade = true
		logger.Error("Memory at memory.high limit - throttling in effect",
			"current_mb", memCurrent/1024/1024,
			"high_mb", memHigh/1024/1024,
			"usage_percent", fmt.Sprintf("%.1f%%", p.MemoryUsagePercent))
	}

	// Calculate estimated optimal memory based on pressure factors
	if len(memoryPressureFactors) > 0 && memHigh > 0 && memHigh != ^uint64(0) {
		// Use the highest pressure factor as our multiplier
		maxFactor := 1.0
		for _, f := range memoryPressureFactors {
			if f > maxFactor {
				maxFactor = f
			}
		}

		// Calculate optimal memory and round up to nearest 256MB
		optimalBytes := uint64(float64(memHigh) * maxFactor)
		optimalMB := (optimalBytes + 256*1024*1024 - 1) / (256 * 1024 * 1024) * 256
		p.EstimatedOptimalMemoryMB = optimalMB
	}

	if p.NeedsMemoryUpgrade {
		logger.Error("Memory upgrade recommended",
			"usage_percent", fmt.Sprintf("%.1f%%", p.MemoryUsagePercent),
			"reclaims", p.MemoryReclaims,
			"optimal_memory_mb", p.EstimatedOptimalMemoryMB)
	}

	return nil
}
