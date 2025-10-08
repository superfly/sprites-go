package resources

import (
	"bufio"
	"os"
	"path/filepath"
	"strings"
	"time"
)

// IOStats contains IO metrics from io.stat
type IOStats struct {
	ReadBytes  uint64 // Total read bytes
	WriteBytes uint64 // Total write bytes
	ReadOps    uint64 // Total read operations
	WriteOps   uint64 // Total write operations
}

// readIOStat reads and parses io.stat file
func (m *Manager) readIOStat() (IOStats, error) {
	f, err := os.Open(filepath.Join(m.cgroupPath, "io.stat"))
	if err != nil {
		return IOStats{}, err
	}
	defer f.Close()

	var stats IOStats
	br := bufio.NewScanner(f)
	for br.Scan() {
		// Example line: "8:0 rbytes=123 wbytes=456 rios=1 wios=2 dbytes=0 dios=0"
		fields := strings.Fields(strings.TrimSpace(br.Text()))
		for _, f := range fields {
			if strings.HasPrefix(f, "rbytes=") {
				stats.ReadBytes += parseUint(strings.TrimPrefix(f, "rbytes="))
			} else if strings.HasPrefix(f, "wbytes=") {
				stats.WriteBytes += parseUint(strings.TrimPrefix(f, "wbytes="))
			} else if strings.HasPrefix(f, "rios=") {
				stats.ReadOps += parseUint(strings.TrimPrefix(f, "rios="))
			} else if strings.HasPrefix(f, "wios=") {
				stats.WriteOps += parseUint(strings.TrimPrefix(f, "wios="))
			}
		}
	}
	if err := br.Err(); err != nil {
		return stats, err
	}

	return stats, nil
}

// tickIO records IO stats to timeseries and accumulates totals
func (m *Manager) tickIO(now time.Time) {
	ioStats, err := m.readIOStat()
	if err != nil {
		// If we can't read IO stats, don't update
		return
	}

	// Record counters to timeseries (they handle delta calculations)
	m.ioReadBytesTotal.Add(now, float64(ioStats.ReadBytes))
	m.ioWriteBytesTotal.Add(now, float64(ioStats.WriteBytes))
	m.ioReadOpsTotal.Add(now, float64(ioStats.ReadOps))
	m.ioWriteOpsTotal.Add(now, float64(ioStats.WriteOps))

	// Accumulate totals for reporting (using timeseries deltas for accuracy)
	// Convert bytes to GB and accumulate
	if readDelta, _, ok := m.ioReadBytesTotal.Increase(); ok && readDelta > 0 {
		deltaGB := readDelta / 1e9
		for {
			oldGB := m.ioReadGB.Load()
			if oldGB == nil {
				if m.ioReadGB.CompareAndSwap(nil, &deltaGB) {
					break
				}
				continue
			}
			newGB := *oldGB + deltaGB
			nv := new(float64)
			*nv = newGB
			if m.ioReadGB.CompareAndSwap(oldGB, nv) {
				break
			}
		}
	}

	if writeDelta, _, ok := m.ioWriteBytesTotal.Increase(); ok && writeDelta > 0 {
		deltaGB := writeDelta / 1e9
		for {
			oldGB := m.ioWriteGB.Load()
			if oldGB == nil {
				if m.ioWriteGB.CompareAndSwap(nil, &deltaGB) {
					break
				}
				continue
			}
			newGB := *oldGB + deltaGB
			nv := new(float64)
			*nv = newGB
			if m.ioWriteGB.CompareAndSwap(oldGB, nv) {
				break
			}
		}
	}

	// Accumulate IOPS
	if readOpsDelta, _, ok := m.ioReadOpsTotal.Increase(); ok && readOpsDelta > 0 {
		m.ioReadOps.Add(int64(readOpsDelta))
	}
	if writeOpsDelta, _, ok := m.ioWriteOpsTotal.Increase(); ok && writeOpsDelta > 0 {
		m.ioWriteOps.Add(int64(writeOpsDelta))
	}
}
