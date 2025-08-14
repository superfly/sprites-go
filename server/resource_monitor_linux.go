//go:build linux

package main

import (
	"bufio"
	"context"
	"errors"
	"fmt"
	"io"
	"log/slog"
	"math"
	"os"
	"path/filepath"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"time"
)

// ResourceMonitor provides lightweight monitoring of CPU, memory, and IO using /proc and cgroups.
// It emits warning logs when resource pressure indicates bottlenecks.
// Linux-only implementation.
type ResourceMonitor struct {
	logger       *slog.Logger
	interval     time.Duration
	cpuThreshold float64 // e.g., 0.9 for 90%
	memThreshold float64 // usage fraction threshold for warnings
	psiSomeCPU   float64 // e.g., warn when cpu PSI some.avg10 > this (fraction)
	psiSomeIO    float64
	psiFullIO    float64

	// CPU previous snapshot
	prevTotalTicks uint64
	prevIdleTicks  uint64
	prevStealTicks uint64
	prevProcTicks  map[int]uint64
	prevProcTime   time.Time

	// cgroup info
	cg *cgroupInfo

	// IO tracking for sustained heavy read/write detection
	prevProcIOBytes         map[int]ioBytesSample
	ioSustainState          map[int]*ioSustain
	heavyReadBpsThreshold   uint64 // bytes/sec considered heavy (reads)
	heavyWriteBpsThreshold  uint64 // bytes/sec considered heavy (writes)
	heavyIOSustainIntervals int    // number of consecutive intervals to consider sustained
}

func NewResourceMonitor(logger *slog.Logger) *ResourceMonitor {
	return &ResourceMonitor{
		logger:          logger,
		interval:        5 * time.Second,
		cpuThreshold:    0.90,
		memThreshold:    0.90,
		psiSomeCPU:      0.10, // 10% average CPU contention over 10s
		psiSomeIO:       0.10, // 10% avg10 IO contention
		psiFullIO:       0.01, // 1% avg10 full IO stall is severe
		prevProcTicks:   make(map[int]uint64),
		prevProcIOBytes: make(map[int]ioBytesSample),
		ioSustainState:  make(map[int]*ioSustain),
		// Conservative defaults to avoid noise; tune if needed
		heavyReadBpsThreshold:   16 * 1024 * 1024, // 16 MiB/s
		heavyWriteBpsThreshold:  16 * 1024 * 1024, // 16 MiB/s
		heavyIOSustainIntervals: 3,                // sustained for ~15s at 5s interval
	}
}

func (rm *ResourceMonitor) Start(ctx context.Context) {
	// Detect cgroup environment once
	rm.cg = detectCgroup()

	// Prime CPU counters
	if tot, idle, steal, err := readProcStatCPU(); err == nil {
		rm.prevTotalTicks, rm.prevIdleTicks, rm.prevStealTicks = tot, idle, steal
	}
	rm.prevProcTime = time.Now()

	go rm.loop(ctx)
}

func (rm *ResourceMonitor) loop(ctx context.Context) {
	ticker := time.NewTicker(rm.interval)
	defer ticker.Stop()

	for {
		select {
		case <-ctx.Done():
			return
		case <-ticker.C:
			// CPU
			rm.checkCPU()
			// Memory
			rm.checkMemory()
			// IO PSI
			rm.checkIO()
		}
	}
}

// ---------------- CPU ----------------

func (rm *ResourceMonitor) checkCPU() {
	// Prefer cgroup CPU capacity when available
	effectiveCPUs := rm.effectiveCPUCount()

	tot, idle, steal, err := readProcStatCPU()
	if err != nil {
		return
	}
	deltaTotal := float64(tot - rm.prevTotalTicks)
	if deltaTotal <= 0 {
		// Avoid div by zero
		return
	}
	deltaIdle := float64(idle - rm.prevIdleTicks)
	deltaSteal := float64(steal - rm.prevStealTicks)

	utilFrac := math.Max(0, (deltaTotal-deltaIdle)/deltaTotal)
	stealFrac := math.Max(0, deltaSteal/deltaTotal)

	// PSI can signal contention even before high utilization
	cpuSome10 := readPSI("/proc/pressure/cpu", "some")

	warn := false
	var reasons []string
	if utilFrac > rm.cpuThreshold {
		warn = true
		reasons = append(reasons, fmt.Sprintf("~%s busy across %.0f CPUs", humanPercent(utilFrac), effectiveCPUs))
	}
	if stealFrac > 0.02 { // 2% steal over window
		warn = true
		reasons = append(reasons, fmt.Sprintf("steal time ~%s (noisy neighbor/oversubscription)", humanPercent(stealFrac)))
	}
	if cpuSome10 > rm.psiSomeCPU {
		warn = true
		reasons = append(reasons, "CPU contention over the last 10s")
	}

	if warn {
		summary := "High CPU usage: " + strings.Join(reasons, "; ") + "."
		top := rm.topCPUConsumers(3)
		if len(top) > 0 {
			var parts []string
			for _, p := range top {
				parts = append(parts, fmt.Sprintf("PID %d (%s) ~%s of a CPU", p.PID, p.Comm, humanPercent(p.CPUFrac)))
			}
			summary += " Top CPU processes: " + strings.Join(parts, ", ") + "."
		}
		rm.logger.Warn(summary)
	}

	// Update prev
	rm.prevTotalTicks, rm.prevIdleTicks, rm.prevStealTicks = tot, idle, steal
}

func (rm *ResourceMonitor) effectiveCPUCount() float64 {
	if rm.cg != nil {
		if n := rm.cg.cpuQuotaCPUs(); n > 0 {
			return n
		}
	}
	return float64(runtime.NumCPU())
}

// ---------------- Memory ----------------

func (rm *ResourceMonitor) checkMemory() {
	var used, limit uint64
	var err error
	if rm.cg != nil && rm.cg.memoryLimitBytes() > 0 {
		used, limit, err = rm.cg.memoryUsageAndLimit()
		if err != nil {
			return
		}
	} else {
		used, limit, err = readSystemMemUsage()
		if err != nil {
			return
		}
	}
	if limit == 0 {
		return
	}
	usageFrac := float64(used) / float64(limit)

	psiSomeMem := readPSI("/proc/pressure/memory", "some")
	warn := false
	var reasons []string
	if usageFrac > rm.memThreshold {
		warn = true
		reasons = append(reasons, fmt.Sprintf("using %s of memory (%s of %s)", humanPercent(usageFrac), humanBytes(used), humanBytes(limit)))
	}
	if psiSomeMem > 0.10 { // reclaim stalls/pressure
		warn = true
		reasons = append(reasons, "memory pressure over the last 10s")
	}
	if warn {
		summary := "High memory usage: " + strings.Join(reasons, "; ") + "."
		top := rm.topMemConsumers(3)
		if len(top) > 0 {
			var parts []string
			for _, p := range top {
				parts = append(parts, fmt.Sprintf("PID %d (%s) RSS %s", p.PID, p.Comm, humanBytes(p.RSSBytes)))
			}
			summary += " Top memory users: " + strings.Join(parts, ", ") + "."
		}
		rm.logger.Warn(summary)
	}
}

// ---------------- IO ----------------

func (rm *ResourceMonitor) checkIO() {
	some := readPSI("/proc/pressure/io", "some")
	full := readPSI("/proc/pressure/io", "full")
	if some > rm.psiSomeIO || full > rm.psiFullIO {
		// Build a simple, plain-English summary
		summary := fmt.Sprintf(
			"Disk IO contention: about %s of the last 10s spent waiting on disk; %s fully stalled.",
			humanPercent(some), humanPercent(full),
		)
		// Attribute to a few IO-heavy processes (best-effort)
		top := rm.topIOConsumers(3)
		if len(top) > 0 {
			var parts []string
			for _, p := range top {
				parts = append(parts, fmt.Sprintf("PID %d (%s)", p.PID, p.Comm))
			}
			summary += " Top IO-heavy processes: " + strings.Join(parts, ", ") + "."
		}
		rm.logger.Warn(summary)
	}

	// Additionally, detect sustained heavy readers/writers based on /proc/[pid]/io rates
	rm.detectSustainedHeavyIO()
}

// ---------------- Helpers ----------------

type procSample struct {
	PID      int
	Comm     string
	CPUFrac  float64
	RSSBytes uint64
	IOBytes  uint64
}

func (rm *ResourceMonitor) candidatePIDs() []int {
	// Prefer cgroup procs
	if rm.cg != nil {
		if pids := rm.cg.procs(); len(pids) > 0 {
			return pids
		}
	}
	// Fallback: all processes (lightweight best-effort: read /proc)
	f, err := os.ReadDir("/proc")
	if err != nil {
		return nil
	}
	var pids []int
	for _, de := range f {
		if !de.IsDir() {
			continue
		}
		if pid, err := strconv.Atoi(de.Name()); err == nil {
			pids = append(pids, pid)
		}
	}
	return pids
}

func (rm *ResourceMonitor) topCPUConsumers(n int) []procSample {
	// Compute per-process CPU fraction over the last sampling window using /proc/[pid]/stat
	pids := rm.candidatePIDs()
	if len(pids) == 0 {
		return nil
	}
	clkTck := float64(sysconfClockTicks())
	if clkTck <= 0 {
		clkTck = 100
	}
	window := time.Since(rm.prevProcTime).Seconds()
	if window <= 0 {
		window = rm.interval.Seconds()
	}
	prev := rm.prevProcTicks
	curr := make(map[int]uint64, len(prev))
	var samples []procSample
	for _, pid := range pids {
		ut, st, comm, err := readProcPIDStat(pid)
		if err != nil {
			continue
		}
		// convert to clock ticks
		ticks := ut + st
		curr[pid] = ticks
		if pt, ok := prev[pid]; ok && ticks >= pt {
			delta := float64(ticks-pt) / clkTck // seconds of CPU
			frac := delta / window              // CPU seconds / elapsed seconds
			if frac < 0 {
				frac = 0
			}
			samples = append(samples, procSample{PID: pid, Comm: comm, CPUFrac: frac})
		}
	}
	// Update prev
	rm.prevProcTicks = curr
	rm.prevProcTime = time.Now()
	// Sort
	sort.Slice(samples, func(i, j int) bool { return samples[i].CPUFrac > samples[j].CPUFrac })
	if len(samples) > n {
		return samples[:n]
	}
	return samples
}

func (rm *ResourceMonitor) topMemConsumers(n int) []procSample {
	pids := rm.candidatePIDs()
	if len(pids) == 0 {
		return nil
	}
	var samples []procSample
	for _, pid := range pids {
		comm := readComm(pid)
		rss, err := readRSSBytes(pid)
		if err != nil {
			continue
		}
		samples = append(samples, procSample{PID: pid, Comm: comm, RSSBytes: rss})
	}
	sort.Slice(samples, func(i, j int) bool { return samples[i].RSSBytes > samples[j].RSSBytes })
	if len(samples) > n {
		return samples[:n]
	}
	return samples
}

func (rm *ResourceMonitor) topIOConsumers(n int) []procSample {
	pids := rm.candidatePIDs()
	if len(pids) == 0 {
		return nil
	}
	var samples []procSample
	for _, pid := range pids {
		comm := readComm(pid)
		r, w := readProcIOBytes(pid)
		bytes := r + w
		if bytes == 0 {
			continue
		}
		samples = append(samples, procSample{PID: pid, Comm: comm, IOBytes: bytes})
	}
	sort.Slice(samples, func(i, j int) bool { return samples[i].IOBytes > samples[j].IOBytes })
	if len(samples) > n {
		return samples[:n]
	}
	return samples
}

// ---------------- proc readers ----------------

func readProcStatCPU() (total, idle, steal uint64, err error) {
	f, err := os.Open("/proc/stat")
	if err != nil {
		return 0, 0, 0, err
	}
	defer f.Close()
	s := bufio.NewScanner(f)
	if !s.Scan() {
		return 0, 0, 0, errors.New("failed to read /proc/stat")
	}
	fields := strings.Fields(s.Text())
	if len(fields) < 8 || fields[0] != "cpu" {
		return 0, 0, 0, errors.New("unexpected /proc/stat format")
	}
	// /proc/stat cpu: user nice system idle iowait irq softirq steal [guest guest_nice]
	vals := make([]uint64, 0, len(fields)-1)
	for _, f := range fields[1:] {
		v, _ := strconv.ParseUint(f, 10, 64)
		vals = append(vals, v)
	}
	var sum uint64
	for _, v := range vals {
		sum += v
	}
	var idleV, stealV uint64
	if len(vals) >= 4 {
		idleV = vals[3]
	}
	if len(vals) >= 8 {
		stealV = vals[7]
	}
	return sum, idleV, stealV, nil
}

func readProcPIDStat(pid int) (utime, stime uint64, comm string, err error) {
	b, err := os.ReadFile(filepath.Join("/proc", strconv.Itoa(pid), "stat"))
	if err != nil {
		return 0, 0, "", err
	}
	// comm can contain spaces and parens; find last ')'
	str := string(b)
	end := strings.LastIndex(str, ")")
	if end == -1 {
		return 0, 0, "", errors.New("bad stat format")
	}
	commPart := str[strings.Index(str, "(")+1 : end]
	rest := strings.Fields(str[end+2:])
	if len(rest) < 15 { // ensure utime (14), stime (15) exist after comm
		return 0, 0, commPart, errors.New("short stat fields")
	}
	// utime is 14th field, stime 15th after comm
	ut, _ := strconv.ParseUint(rest[11], 10, 64)
	st, _ := strconv.ParseUint(rest[12], 10, 64)
	return ut, st, commPart, nil
}

func readRSSBytes(pid int) (uint64, error) {
	// Prefer /proc/[pid]/statm rss * page_size
	b, err := os.ReadFile(filepath.Join("/proc", strconv.Itoa(pid), "statm"))
	if err != nil {
		return 0, err
	}
	parts := strings.Fields(string(b))
	if len(parts) < 2 {
		return 0, errors.New("bad statm")
	}
	rssPages, _ := strconv.ParseUint(parts[1], 10, 64)
	pageSize := uint64(os.Getpagesize())
	return rssPages * pageSize, nil
}

func readProcIOBytes(pid int) (readBytes, writeBytes uint64) {
	f, err := os.Open(filepath.Join("/proc", strconv.Itoa(pid), "io"))
	if err != nil {
		return 0, 0
	}
	defer f.Close()
	var r, w uint64
	sc := bufio.NewScanner(f)
	for sc.Scan() {
		line := sc.Text()
		if strings.HasPrefix(line, "read_bytes:") {
			fmt.Sscanf(line, "read_bytes:%d", &r)
		} else if strings.HasPrefix(line, "write_bytes:") {
			fmt.Sscanf(line, "write_bytes:%d", &w)
		}
	}
	return r, w
}

type procIOStats struct {
	ReadBytes   uint64
	WriteBytes  uint64
	SysReadOps  uint64
	SysWriteOps uint64
	RChar       uint64
	WChar       uint64
}

// readProcIOStats reads a richer set of IO stats from /proc/[pid]/io.
// Fields are best-effort and may be unavailable on some kernels.
func readProcIOStats(pid int) procIOStats {
	f, err := os.Open(filepath.Join("/proc", strconv.Itoa(pid), "io"))
	if err != nil {
		return procIOStats{}
	}
	defer f.Close()
	var st procIOStats
	sc := bufio.NewScanner(f)
	for sc.Scan() {
		line := sc.Text()
		switch {
		case strings.HasPrefix(line, "read_bytes:"):
			fmt.Sscanf(line, "read_bytes:%d", &st.ReadBytes)
		case strings.HasPrefix(line, "write_bytes:"):
			fmt.Sscanf(line, "write_bytes:%d", &st.WriteBytes)
		case strings.HasPrefix(line, "syscr:"):
			fmt.Sscanf(line, "syscr:%d", &st.SysReadOps)
		case strings.HasPrefix(line, "syscw:"):
			fmt.Sscanf(line, "syscw:%d", &st.SysWriteOps)
		case strings.HasPrefix(line, "rchar:"):
			fmt.Sscanf(line, "rchar:%d", &st.RChar)
		case strings.HasPrefix(line, "wchar:"):
			fmt.Sscanf(line, "wchar:%d", &st.WChar)
		}
	}
	return st
}

// ---------------- sustained IO detection ----------------

type ioBytesSample struct {
	ReadBytes   uint64
	WriteBytes  uint64
	SysReadOps  uint64
	SysWriteOps uint64
	RChar       uint64
	WChar       uint64
}

type ioRateSample struct {
	PID        int
	Comm       string
	ReadBps    uint64
	WriteBps   uint64
	ReadOpsPS  float64
	WriteOpsPS float64
}

type ioSustain struct {
	ConsecutiveReadIntervals  int
	ConsecutiveWriteIntervals int
	ReadLogged                bool
	WriteLogged               bool
}

func (rm *ResourceMonitor) detectSustainedHeavyIO() {
	pids := rm.candidatePIDs()
	if len(pids) == 0 {
		return
	}
	intervalSeconds := rm.interval.Seconds()
	if intervalSeconds <= 0 {
		intervalSeconds = 5
	}

	// Compute per-process rates
	var rates []ioRateSample
	nextPrev := make(map[int]ioBytesSample, len(pids))
	for _, pid := range pids {
		comm := readComm(pid)
		stats := readProcIOStats(pid)
		nextPrev[pid] = ioBytesSample{
			ReadBytes:   stats.ReadBytes,
			WriteBytes:  stats.WriteBytes,
			SysReadOps:  stats.SysReadOps,
			SysWriteOps: stats.SysWriteOps,
			RChar:       stats.RChar,
			WChar:       stats.WChar,
		}
		prev, ok := rm.prevProcIOBytes[pid]
		if !ok {
			continue
		}
		// Handle counter reset (pid recycled or wrap)
		if stats.ReadBytes < prev.ReadBytes || stats.WriteBytes < prev.WriteBytes ||
			stats.SysReadOps < prev.SysReadOps || stats.SysWriteOps < prev.SysWriteOps ||
			stats.RChar < prev.RChar || stats.WChar < prev.WChar {
			continue
		}
		rDelta := stats.ReadBytes - prev.ReadBytes
		wDelta := stats.WriteBytes - prev.WriteBytes
		ropsDelta := stats.SysReadOps - prev.SysReadOps
		wopsDelta := stats.SysWriteOps - prev.SysWriteOps
		if rDelta == 0 && wDelta == 0 {
			continue
		}
		rBps := uint64(float64(rDelta) / intervalSeconds)
		wBps := uint64(float64(wDelta) / intervalSeconds)
		rates = append(rates, ioRateSample{PID: pid, Comm: comm, ReadBps: rBps, WriteBps: wBps, ReadOpsPS: float64(ropsDelta) / intervalSeconds, WriteOpsPS: float64(wopsDelta) / intervalSeconds})
	}
	rm.prevProcIOBytes = nextPrev

	// Update sustain state and log transitions
	for _, s := range rates {
		st := rm.ioSustainState[s.PID]
		if st == nil {
			st = &ioSustain{}
			rm.ioSustainState[s.PID] = st
		}
		// Reads
		if s.ReadBps >= rm.heavyReadBpsThreshold {
			st.ConsecutiveReadIntervals++
			if st.ConsecutiveReadIntervals >= rm.heavyIOSustainIntervals && !st.ReadLogged {
				sustainedFor := float64(st.ConsecutiveReadIntervals) * intervalSeconds
				msg := fmt.Sprintf(
					"Sustained heavy READS: PID %d (%s) ~%s (~%.0f ops/s) for %s.",
					s.PID, s.Comm, humanBytesPerSec(s.ReadBps), s.ReadOpsPS, humanDurationSeconds(sustainedFor),
				)
				rm.logger.Warn(msg)
				st.ReadLogged = true
			}
		} else {
			st.ConsecutiveReadIntervals = 0
			st.ReadLogged = false
		}
		// Writes
		if s.WriteBps >= rm.heavyWriteBpsThreshold {
			st.ConsecutiveWriteIntervals++
			if st.ConsecutiveWriteIntervals >= rm.heavyIOSustainIntervals && !st.WriteLogged {
				sustainedFor := float64(st.ConsecutiveWriteIntervals) * intervalSeconds
				msg := fmt.Sprintf(
					"Sustained heavy WRITES: PID %d (%s) ~%s (~%.0f ops/s) for %s.",
					s.PID, s.Comm, humanBytesPerSec(s.WriteBps), s.WriteOpsPS, humanDurationSeconds(sustainedFor),
				)
				rm.logger.Warn(msg)
				st.WriteLogged = true
			}
		} else {
			st.ConsecutiveWriteIntervals = 0
			st.WriteLogged = false
		}
	}
}

// ---------------- formatting helpers ----------------

func humanPercent(frac float64) string {
	if frac < 0 {
		frac = 0
	}
	// frac is 0..1
	return fmt.Sprintf("%.0f%%", frac*100)
}

func humanBytesPerSec(bps uint64) string {
	const (
		kb = 1024
		mb = 1024 * kb
		gb = 1024 * mb
	)
	switch {
	case bps >= gb:
		return fmt.Sprintf("%.1f GiB/s", float64(bps)/float64(gb))
	case bps >= mb:
		return fmt.Sprintf("%.1f MiB/s", float64(bps)/float64(mb))
	case bps >= kb:
		return fmt.Sprintf("%.1f KiB/s", float64(bps)/float64(kb))
	default:
		return fmt.Sprintf("%d B/s", bps)
	}
}

func humanDurationSeconds(secondsFloat float64) string {
	// Round to nearest second for clean output
	if secondsFloat < 0 {
		secondsFloat = 0
	}
	sec := int(secondsFloat + 0.5)
	return fmt.Sprintf("%ds", sec)
}

func humanBytes(b uint64) string {
	const (
		kb = 1024
		mb = 1024 * kb
		gb = 1024 * mb
	)
	switch {
	case b >= gb:
		return fmt.Sprintf("%.1f GiB", float64(b)/float64(gb))
	case b >= mb:
		return fmt.Sprintf("%.1f MiB", float64(b)/float64(mb))
	case b >= kb:
		return fmt.Sprintf("%.1f KiB", float64(b)/float64(kb))
	default:
		return fmt.Sprintf("%d B", b)
	}
}

func readPSI(path string, class string) float64 {
	f, err := os.Open(path)
	if err != nil {
		return 0
	}
	defer f.Close()
	b, _ := io.ReadAll(f)
	// Example: some avg10=0.00 avg60=0.00 avg300=0.00 total=0
	for _, line := range strings.Split(string(b), "\n") {
		if strings.HasPrefix(line, class+" ") {
			parts := strings.Fields(line)
			for _, p := range parts {
				if strings.HasPrefix(p, "avg10=") {
					vStr := strings.TrimPrefix(p, "avg10=")
					v, _ := strconv.ParseFloat(vStr, 64)
					return v / 100.0 // kernel reports percentage
				}
			}
		}
	}
	return 0
}

func readSystemMemUsage() (used, limit uint64, err error) {
	// Minimal parse of /proc/meminfo: MemTotal and MemAvailable
	f, err := os.Open("/proc/meminfo")
	if err != nil {
		return 0, 0, err
	}
	defer f.Close()
	var totalKB, availKB uint64
	s := bufio.NewScanner(f)
	for s.Scan() {
		line := s.Text()
		if strings.HasPrefix(line, "MemTotal:") {
			fmt.Sscanf(line, "MemTotal:%d kB", &totalKB)
		} else if strings.HasPrefix(line, "MemAvailable:") {
			fmt.Sscanf(line, "MemAvailable:%d kB", &availKB)
		}
	}
	limit = totalKB * 1024
	if totalKB == 0 {
		return 0, 0, errors.New("MemTotal not found")
	}
	if availKB > totalKB {
		availKB = 0
	}
	used = (totalKB - availKB) * 1024
	return used, limit, nil
}

func readComm(pid int) string {
	b, err := os.ReadFile(filepath.Join("/proc", strconv.Itoa(pid), "comm"))
	if err != nil {
		return ""
	}
	return strings.TrimSpace(string(b))
}

// ---------------- cgroup helpers ----------------

type cgroupInfo struct {
	isV2 bool
	// mount points
	root string // unified for v2; base for v1
	// cgroup relative path of this process
	selfPath string
}

func detectCgroup() *cgroupInfo {
	// Detect v2
	if _, err := os.Stat("/sys/fs/cgroup/cgroup.controllers"); err == nil {
		cg := &cgroupInfo{isV2: true, root: "/sys/fs/cgroup"}
		cg.selfPath = cgroupSelfPath(true)
		return cg
	}
	// v1 fallback: root paths can vary; use /proc/self/cgroup
	cg := &cgroupInfo{isV2: false, root: "/sys/fs/cgroup"}
	cg.selfPath = cgroupSelfPath(false)
	return cg
}

func cgroupSelfPath(v2 bool) string {
	b, err := os.ReadFile("/proc/self/cgroup")
	if err != nil {
		return ""
	}
	lines := strings.Split(string(b), "\n")
	if v2 {
		for _, l := range lines {
			// 0::<path>
			parts := strings.SplitN(l, ":", 3)
			if len(parts) == 3 && parts[0] == "0" {
				return parts[2]
			}
		}
		return ""
	}
	// v1: pick memory or cpuacct path (any is fine to resolve)
	for _, l := range lines {
		parts := strings.SplitN(l, ":", 3)
		if len(parts) != 3 {
			continue
		}
		// choose first non-empty path
		if parts[2] != "" {
			return parts[2]
		}
	}
	return ""
}

func (cg *cgroupInfo) cpuQuotaCPUs() float64 {
	if cg == nil {
		return 0
	}
	if cg.isV2 {
		b, err := os.ReadFile(filepath.Join(cg.root, cg.selfPath, "cpu.max"))
		if err != nil {
			return 0
		}
		// format: "max <period>" or "<quota> <period>"
		parts := strings.Fields(string(b))
		if len(parts) != 2 {
			return 0
		}
		if parts[0] == "max" {
			return 0
		}
		quota, _ := strconv.ParseFloat(strings.TrimSpace(parts[0]), 64)
		period, _ := strconv.ParseFloat(strings.TrimSpace(parts[1]), 64)
		if quota <= 0 || period <= 0 {
			return 0
		}
		return quota / period
	}
	// v1
	quotaB, err1 := os.ReadFile(filepath.Join(cg.root, "cpu", cg.selfPath, "cpu.cfs_quota_us"))
	periodB, err2 := os.ReadFile(filepath.Join(cg.root, "cpu", cg.selfPath, "cpu.cfs_period_us"))
	if err1 != nil || err2 != nil {
		return 0
	}
	quota, _ := strconv.ParseFloat(strings.TrimSpace(string(quotaB)), 64)
	period, _ := strconv.ParseFloat(strings.TrimSpace(string(periodB)), 64)
	if quota <= 0 || period <= 0 {
		return 0
	}
	return quota / period
}

func (cg *cgroupInfo) procs() []int {
	if cg == nil {
		return nil
	}
	paths := []string{}
	if cg.isV2 {
		paths = []string{filepath.Join(cg.root, cg.selfPath, "cgroup.procs")}
	} else {
		// v1 controllers may have separate procs files; try common ones
		paths = []string{
			filepath.Join(cg.root, "cpuacct", cg.selfPath, "cgroup.procs"),
			filepath.Join(cg.root, "cpu", cg.selfPath, "cgroup.procs"),
			filepath.Join(cg.root, "memory", cg.selfPath, "cgroup.procs"),
		}
	}
	var out []int
	for _, p := range paths {
		b, err := os.ReadFile(p)
		if err != nil {
			continue
		}
		for _, line := range strings.Split(strings.TrimSpace(string(b)), "\n") {
			if line == "" {
				continue
			}
			if pid, err := strconv.Atoi(strings.TrimSpace(line)); err == nil {
				out = append(out, pid)
			}
		}
	}
	return out
}

func (cg *cgroupInfo) memoryLimitBytes() uint64 {
	if cg == nil {
		return 0
	}
	if cg.isV2 {
		b, err := os.ReadFile(filepath.Join(cg.root, cg.selfPath, "memory.max"))
		if err != nil {
			return 0
		}
		s := strings.TrimSpace(string(b))
		if s == "max" || s == "" {
			return 0
		}
		v, _ := strconv.ParseUint(s, 10, 64)
		return v
	}
	b, err := os.ReadFile(filepath.Join(cg.root, "memory", cg.selfPath, "memory.limit_in_bytes"))
	if err != nil {
		return 0
	}
	v, _ := strconv.ParseUint(strings.TrimSpace(string(b)), 10, 64)
	return v
}

func (cg *cgroupInfo) memoryUsageAndLimit() (used, limit uint64, err error) {
	if cg == nil {
		return 0, 0, errors.New("no cgroup")
	}
	if cg.isV2 {
		ub, err1 := os.ReadFile(filepath.Join(cg.root, cg.selfPath, "memory.current"))
		lb, err2 := os.ReadFile(filepath.Join(cg.root, cg.selfPath, "memory.max"))
		if err1 != nil || err2 != nil {
			return 0, 0, errors.New("missing memory files")
		}
		used, _ = strconv.ParseUint(strings.TrimSpace(string(ub)), 10, 64)
		s := strings.TrimSpace(string(lb))
		if s == "max" || s == "" {
			// No limit; fallback to system
			return readSystemMemUsage()
		}
		limit, _ = strconv.ParseUint(s, 10, 64)
		return used, limit, nil
	}
	ub, err1 := os.ReadFile(filepath.Join(cg.root, "memory", cg.selfPath, "memory.usage_in_bytes"))
	lb, err2 := os.ReadFile(filepath.Join(cg.root, "memory", cg.selfPath, "memory.limit_in_bytes"))
	if err1 != nil || err2 != nil {
		return 0, 0, errors.New("missing memory files")
	}
	used, _ = strconv.ParseUint(strings.TrimSpace(string(ub)), 10, 64)
	limit, _ = strconv.ParseUint(strings.TrimSpace(string(lb)), 10, 64)
	if limit == 0 || limit > (1<<62) { // some kernels use very large number for no limit
		return readSystemMemUsage()
	}
	return used, limit, nil
}

// ---------------- platform utils ----------------

func sysconfClockTicks() int64 {
	// Try to read from sysfs if available; fallback to 100
	// On Linux, USER_HZ is commonly 100. Using 100 is acceptable for coarse monitoring.
	return 100
}
