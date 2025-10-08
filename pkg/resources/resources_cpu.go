package resources

import (
	"bufio"
	"errors"
	"fmt"
	"io"
	"log/slog"
	"math"
	"os"
	"path/filepath"
	"strings"
	"time"
)

// SetCPUQuota writes cpu.max with quota/period. Pass quota<=0 to set "max" (no limit).
// Example: quota=100ms, period=100ms gives 100% of one CPU; 50ms/100ms gives 50% of one CPU.
func (m *Manager) SetCPUQuota(quota time.Duration, period time.Duration) error {
	var content string
	if quota <= 0 {
		// Remove limit entirely
		content = "max"
	} else {
		content = fmt.Sprintf("%d %d", quota.Microseconds(), period.Microseconds())
	}
	return m.writeFile("cpu.max", content+"\n")
}

// ReadCPUStat reads and parses cpu.stat file
func (m *Manager) ReadCPUStat() (CPUStat, error) {
	f, err := os.Open(filepath.Join(m.cgroupPath, "cpu.stat"))
	if err != nil {
		return CPUStat{}, err
	}
	defer f.Close()
	var st CPUStat
	br := bufio.NewReader(f)
	for {
		line, err := br.ReadString('\n')
		if len(line) > 0 {
			key, val, ok := strings.Cut(strings.TrimSpace(line), " ")
			if ok {
				switch key {
				case "usage_usec":
					st.UsageTotal = time.Duration(parseUint(val)) * time.Microsecond
				case "user_usec":
					st.User = time.Duration(parseUint(val)) * time.Microsecond
				case "system_usec":
					st.System = time.Duration(parseUint(val)) * time.Microsecond
				case "nr_periods":
					st.NrPeriods = parseUint(val)
				case "nr_throttled":
					st.NrThrottled = parseUint(val)
				case "throttled_usec":
					st.ThrottledTime = time.Duration(parseUint(val)) * time.Microsecond
				}
			}
		}
		if errors.Is(err, io.EOF) {
			break
		}
		if err != nil {
			return st, err
		}
	}
	return st, nil
}

// PredictCPUUsage predicts total CPU usage at a future time.
// Returns total CPU seconds consumed (since boot) at the given time.
func (m *Manager) PredictCPUUsage(t time.Time) (seconds float64, confidence float64, ok bool) {
	// Note: We don't actually track CPU usage total in a timeseries
	// because it's monotonic from the kernel. We track CPU throttle percentage instead.
	// For now, return not ok - this prediction isn't meaningful for total usage.
	return 0, 0, false
}

// tickCPU updates CPU throttle tracking in timeseries and global CPU balance.
// CPU banking and deficit are tracked globally by the CPUBalance singleton.
func (m *Manager) tickCPU(now time.Time, elapsed time.Duration) {
	st, err := m.ReadCPUStat()
	if err == nil {
		// Update last CPU usage for delta calculation
		m.lastCPUUsage.Store(st.UsageTotal.Nanoseconds())

		// Update global CPU balance with this cgroup's usage (unless disabled)
		// The global CPU balance is initialized once on first access via GetCPUBalance().
		// When multiple managers are used, skipGlobalCPUBalance should be set to true
		// and the aggregation should be done externally (e.g., via MonitorGroup).
		if !m.skipGlobalCPUBalance {
			GetCPUBalance().Tick(now, st.UsageTotal)
		}

		// Record CPU throttle percentage
		if st.NrPeriods > 0 {
			throttlePct := float64(st.NrThrottled) / float64(st.NrPeriods) * 100
			m.cpuThrottlePct.Add(now, throttlePct)
		}
	}
}

// checkCPUPressure analyzes CPU pressure and updates the ResourcePressure struct.
// Returns true if CPU pressure checks should continue (no fatal errors).
func (m *Manager) checkCPUPressure(p *ResourcePressure, logger *slog.Logger) error {
	cpuStat, err := m.ReadCPUStat()
	if err != nil {
		return err
	}

	// Fill in CPU banking info from global singleton
	cb := GetCPUBalance()
	p.CPUBankBalance = cb.Balance()
	p.CPUBankMax = cb.MaxBank()
	p.CPUDeficit = cb.Deficit()
	p.CPUAccrualRate = cb.AccrualRate()

	// Use current throttle percentage, but also check trend
	if cpuStat.NrPeriods > 0 {
		p.CPUThrottledPercent = float64(cpuStat.NrThrottled) / float64(cpuStat.NrPeriods) * 100

		// Consider it throttled if more than 10% of periods were throttled
		p.CPUThrottled = p.CPUThrottledPercent > 10
		// Need upgrade if throttled more than 25% of the time
		p.NeedsCPUUpgrade = p.CPUThrottledPercent > 25

		// Estimate demand rate based on throttling
		if cpuStat.ThrottledTime > 0 || p.CPUThrottledPercent > 0 {
			// If we're throttled X% of the time, demand exceeds supply by that ratio
			// Demand rate = accrual rate / (1 - throttle_percent/100)
			if p.CPUThrottledPercent < 100 {
				p.CPUDemandRate = time.Duration(float64(p.CPUAccrualRate) / (1 - p.CPUThrottledPercent/100))
			} else {
				// 100% throttled means infinite demand
				p.CPUDemandRate = time.Duration(math.MaxInt64)
			}
		} else {
			// No throttling, demand equals accrual
			p.CPUDemandRate = p.CPUAccrualRate
		}

		if p.CPUThrottled {
			logger.Warn("CPU throttling detected - demand exceeds quota",
				"throttled_percent", fmt.Sprintf("%.1f%%", p.CPUThrottledPercent),
				"throttled_periods", cpuStat.NrThrottled,
				"total_periods", cpuStat.NrPeriods,
				"throttled_time", cpuStat.ThrottledTime,
				"bank_balance", p.CPUBankBalance,
				"bank_max", p.CPUBankMax,
				"accrual_rate", fmt.Sprintf("%.2f ms/s", p.CPUAccrualRate.Seconds()*1000),
				"demand_rate", fmt.Sprintf("%.2f ms/s", p.CPUDemandRate.Seconds()*1000))
		}

		if p.NeedsCPUUpgrade {
			// Calculate time until bank exhaustion based on current trends
			var timeToExhaustion string
			if p.CPUDemandRate > p.CPUAccrualRate && p.CPUBankBalance > 0 {
				deficitRate := p.CPUDemandRate - p.CPUAccrualRate
				ttx := time.Duration(float64(p.CPUBankBalance) / float64(deficitRate) * float64(time.Second))
				timeToExhaustion = ttx.String()
			} else if p.CPUBankBalance <= 0 {
				timeToExhaustion = "exhausted now"
			} else {
				timeToExhaustion = "never (demand <= accrual)"
			}

			logger.Error("CPU upgrade needed - unsustainable demand",
				"cgroup", filepath.Base(m.cgroupPath),
				"throttled_percent", fmt.Sprintf("%.1f%%", p.CPUThrottledPercent),
				"bank_balance", p.CPUBankBalance.String(),
				"time_to_exhaustion", timeToExhaustion,
				"accumulated_deficit", p.CPUDeficit.String())
		}
	}

	// Check if bank is exhausted and deficit exists
	if p.CPUBankBalance == 0 && p.CPUDeficit > 0 {
		p.NeedsCPUUpgrade = true
		logger.Error("CPU bank exhausted with deficit",
			"cgroup", filepath.Base(m.cgroupPath),
			"bank_balance", p.CPUBankBalance.String(),
			"deficit", p.CPUDeficit.String(),
			"throttled_percent", fmt.Sprintf("%.1f%%", p.CPUThrottledPercent))

		// If demand wasn't calculated yet, estimate it's at least 50% higher than accrual
		if p.CPUDemandRate == 0 {
			p.CPUDemandRate = time.Duration(float64(p.CPUAccrualRate) * 1.5)
		}
	}

	// Log upgrade recommendations
	if p.NeedsCPUUpgrade {
		// Calculate quota increase needed to balance demand
		quotaIncrease := time.Duration(0)
		if p.CPUDemandRate > p.CPUAccrualRate {
			quotaIncrease = p.CPUDemandRate - p.CPUAccrualRate
		}

		logger.Error("CPU upgrade recommended - increase quota to balance demand",
			"throttled_percent", fmt.Sprintf("%.1f%%", p.CPUThrottledPercent),
			"bank_balance", p.CPUBankBalance,
			"accumulated_deficit", p.CPUDeficit,
			"current_accrual", fmt.Sprintf("%.2f ms/s", p.CPUAccrualRate.Seconds()*1000),
			"demand_rate", fmt.Sprintf("%.2f ms/s", p.CPUDemandRate.Seconds()*1000),
			"quota_increase_needed", fmt.Sprintf("%.2f ms/s", quotaIncrease.Seconds()*1000))
	}

	return nil
}
