package resources

import (
	"runtime"
	"sync"
	"sync/atomic"
	"time"
)

// CPUBalance is a global singleton that tracks CPU banking at the VM level.
// It represents the total CPU quota accrual and consumption across the entire VM,
// independent of individual cgroup monitoring.
type CPUBalance struct {
	cpus          int32         // logical CPUs to budget against
	accruePer80ms time.Duration // tokens added per CPU every 80ms (default 5ms)
	maxBank       time.Duration // maximum bankable CPU time (default 500s)

	// trackers (atomics allow safe reads without locks)
	bankedNanos  atomic.Int64 // current bank balance in nanoseconds
	lastCPUUsage atomic.Int64 // last observed total cpu usage in nanoseconds
	lastSampleNS atomic.Int64 // last sample wall time (Unix nano)

	// CPU deficit tracking (accumulates when demand > supply + bank)
	cpuDeficit atomic.Int64 // accumulated CPU deficit in nanoseconds

	// Mutex to protect Tick operations from concurrent access
	tickMu sync.Mutex
}

var (
	globalCPUBalance     *CPUBalance
	globalCPUBalanceOnce sync.Once
)

// GetCPUBalance returns the global CPU balance singleton.
// It's initialized on first call with system CPU count.
func GetCPUBalance() *CPUBalance {
	globalCPUBalanceOnce.Do(func() {
		cpuCount := runtime.NumCPU()
		globalCPUBalance = &CPUBalance{
			cpus:          int32(cpuCount),
			accruePer80ms: 5 * time.Millisecond,
			maxBank:       500 * time.Second,
		}
		// Initialize last sample time to now
		globalCPUBalance.lastSampleNS.Store(time.Now().UnixNano())
	})
	return globalCPUBalance
}

// Balance returns the currently banked CPU time available at the VM level.
func (cb *CPUBalance) Balance() time.Duration {
	return time.Duration(cb.bankedNanos.Load())
}

// Deficit returns the total accumulated CPU deficit at the VM level.
// This represents CPU time that processes wanted but couldn't get even with banking.
func (cb *CPUBalance) Deficit() time.Duration {
	return time.Duration(cb.cpuDeficit.Load())
}

// MaxBank returns the maximum bankable CPU time.
func (cb *CPUBalance) MaxBank() time.Duration {
	return cb.maxBank
}

// AccrualRate returns the rate at which CPU quota accrues per second.
func (cb *CPUBalance) AccrualRate() time.Duration {
	// accruePer80ms per CPU per 80ms, scaled to per second
	return time.Duration(float64(cb.accruePer80ms) * float64(cb.cpus) * (1000.0 / 80.0))
}

// Tick updates the CPU balance based on elapsed time and total CPU usage.
// This should be called periodically (e.g., every 5-10 seconds).
// The totalCPUUsage is the cumulative CPU usage from all monitored cgroups.
// This method is thread-safe and can be called concurrently.
func (cb *CPUBalance) Tick(now time.Time, totalCPUUsage time.Duration) {
	// Protect the entire tick operation with a mutex to prevent race conditions
	cb.tickMu.Lock()
	defer cb.tickMu.Unlock()

	// Calculate elapsed time since last tick
	lastWallNS := cb.lastSampleNS.Load()
	elapsed := time.Duration(now.UnixNano() - lastWallNS)
	if elapsed < 0 {
		elapsed = 0
	}

	// Accrue tokens based on elapsed time
	if elapsed > 0 {
		// tokens per ns = (accruePer80ms / 80ms) per CPU
		accruePerNS := float64(cb.accruePer80ms) / float64(80*time.Millisecond)
		tokens := time.Duration(accruePerNS * float64(elapsed) * float64(atomic.LoadInt32(&cb.cpus)))
		newBank := time.Duration(cb.bankedNanos.Add(tokens.Nanoseconds()))
		// Clamp to maxBank
		if newBank > cb.maxBank {
			cb.bankedNanos.Store(cb.maxBank.Nanoseconds())
		}
	}

	// Subtract actual usage delta
	prev := time.Duration(cb.lastCPUUsage.Swap(totalCPUUsage.Nanoseconds()))
	delta := totalCPUUsage - prev
	if delta > 0 {
		remaining := cb.bankedNanos.Add(-delta.Nanoseconds())
		if time.Duration(remaining) < 0 {
			// We've exhausted the bank and gone into deficit
			deficit := -remaining
			cb.cpuDeficit.Add(deficit)
			cb.bankedNanos.Store(0)
		}
	}

	// Update last sample time
	cb.lastSampleNS.Store(now.UnixNano())
}

// ResetTimeTracking resets the time tracking to the current moment.
// This should be called after suspend/resume to prevent crediting CPU time
// for the period when the system was suspended.
func (cb *CPUBalance) ResetTimeTracking() {
	now := time.Now()
	cb.lastSampleNS.Store(now.UnixNano())
}

// Reset clears all accumulated state and resets to initial values.
// This is primarily for testing purposes.
func (cb *CPUBalance) Reset() {
	cb.bankedNanos.Store(0)
	cb.lastCPUUsage.Store(0)
	cb.lastSampleNS.Store(time.Now().UnixNano())
	cb.cpuDeficit.Store(0)
}

// ResetGlobalCPUBalance resets the global CPU balance singleton.
// This is for testing purposes only.
func ResetGlobalCPUBalance() {
	if globalCPUBalance != nil {
		globalCPUBalance.Reset()
	}
}
