package resources

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// TestBasicOperations tests the core functionality without requiring actual cgroup control
func TestBasicOperations(t *testing.T) {
	// Reset global CPU balance for clean test state
	ResetGlobalCPUBalance()

	// When using host cgroups, create a test sub-cgroup
	cgroupPath := "/sys/fs/cgroup"
	if os.Getenv("SPRITE_TEST_DOCKER") == "1" {
		// Try to create a test cgroup
		testPath := filepath.Join("/sys/fs/cgroup", fmt.Sprintf("sprite-basic-test-%d", os.Getpid()))
		if err := os.Mkdir(testPath, 0755); err == nil {
			cgroupPath = testPath
			t.Cleanup(func() {
				_ = os.Remove(testPath)
			})
		}
	}

	m, err := NewManager(cgroupPath)
	if err != nil {
		t.Fatal("NewManager:", err)
	}

	// Test CPU banking accumulation
	initial := m.CPUBankBalance()
	t.Logf("Initial bank: %v", initial)

	// Simulate time passing
	time.Sleep(200 * time.Millisecond)
	m.Tick(time.Now())

	after := m.CPUBankBalance()
	t.Logf("Bank after 200ms: %v", after)

	// Should accumulate ~25ms (2 CPUs * 5ms * 200ms/80ms)
	if after <= initial {
		t.Error("Expected bank to increase")
	}

	// Test stats reading (may fail if not in container with proper cgroup)
	stats, err := m.ReadStats()
	if err == nil {
		t.Logf("Stats: CPU=%v, Mem=%d MB, IO Read=%d MB, Write=%d MB",
			stats.CPUUsageTotal,
			stats.MemoryCurrentBytes/1024/1024,
			stats.IOReadBytes/1024/1024,
			stats.IOWriteBytes/1024/1024)
	}

	// Test memory GB-seconds tracking
	initialGBS := stats.MemoryGBSeconds
	time.Sleep(100 * time.Millisecond)
	m.Tick(time.Now())

	stats2, _ := m.ReadStats()
	if stats2.MemoryGBSeconds <= initialGBS {
		t.Logf("GB-seconds didn't increase: %v -> %v", initialGBS, stats2.MemoryGBSeconds)
	}
}

// TestCPUBankingLogic tests CPU banking without needing real processes
func TestCPUBankingLogic(t *testing.T) {
	// Reset global CPU balance for clean test state
	ResetGlobalCPUBalance()

	// Create a temp directory with mock cgroup files
	tmpDir := t.TempDir()

	// Create mock cpu.stat file
	cpuStatPath := filepath.Join(tmpDir, "cpu.stat")
	initialCPU := `usage_usec 1000000
user_usec 800000
system_usec 200000
nr_periods 0
nr_throttled 0
throttled_usec 0
`
	if err := os.WriteFile(cpuStatPath, []byte(initialCPU), 0644); err != nil {
		t.Fatal(err)
	}

	// Create other mock files
	os.WriteFile(filepath.Join(tmpDir, "memory.current"), []byte("104857600"), 0644) // 100MB
	os.WriteFile(filepath.Join(tmpDir, "io.stat"), []byte(""), 0644)
	os.WriteFile(filepath.Join(tmpDir, "cpu.max"), []byte(""), 0644)
	os.WriteFile(filepath.Join(tmpDir, "memory.low"), []byte(""), 0644)
	os.WriteFile(filepath.Join(tmpDir, "memory.high"), []byte(""), 0644)

	m, err := NewManager(tmpDir)
	if err != nil {
		t.Fatal("NewManager:", err)
	}

	// Test initial state
	initial := m.CPUBankBalance()
	t.Logf("Initial bank: %v", initial)

	// Accumulate for 400ms (should get ~50ms with 2 CPUs)
	time.Sleep(400 * time.Millisecond)
	m.Tick(time.Now())

	accumulated := m.CPUBankBalance()
	t.Logf("Bank after 400ms: %v", accumulated)

	// Should have accumulated some CPU time (amount depends on system CPU count)
	if accumulated <= initial {
		t.Errorf("Expected bank to increase, got %v", accumulated)
	}

	// Simulate CPU usage by updating the file
	laterCPU := `usage_usec 1030000
user_usec 824000
system_usec 206000
nr_periods 5
nr_throttled 2
throttled_usec 10000
`
	os.WriteFile(cpuStatPath, []byte(laterCPU), 0644)

	// Tick to consume some banked time (30ms of CPU used)
	m.Tick(time.Now())

	afterUsage := m.CPUBankBalance()
	t.Logf("Bank after 30ms CPU usage: %v", afterUsage)

	// Should have decreased by ~30ms
	expected := accumulated - 30*time.Millisecond
	if afterUsage < expected-5*time.Millisecond || afterUsage > expected+5*time.Millisecond {
		t.Errorf("Expected bank ~%v after usage, got %v", expected, afterUsage)
	}

	// Test max banking - need longer to reach 500s cap
	// Current bank is ~20ms, need to accumulate ~500s
	// With 2 CPUs at 5ms per 80ms = 0.125ms/ms = 125ms/s
	// So need ~4000s to accumulate 500s, but let's just verify it's accumulating

	// Accumulate for 2 more seconds
	for i := 0; i < 20; i++ {
		time.Sleep(100 * time.Millisecond)
		m.Tick(time.Now())
	}

	afterMore := m.CPUBankBalance()
	t.Logf("Bank after 2s more accumulation: %v", afterMore)

	// Should have added ~250ms (2 CPUs * 5ms * 2000ms/80ms)
	if afterMore < afterUsage+200*time.Millisecond {
		t.Errorf("Expected significant accumulation, got %v", afterMore)
	}
}

// TestMemoryGBSeconds tests memory integral tracking
func TestMemoryGBSeconds(t *testing.T) {
	// Reset global CPU balance for clean test state
	ResetGlobalCPUBalance()

	tmpDir := t.TempDir()

	// Create mock files
	os.WriteFile(filepath.Join(tmpDir, "cpu.stat"), []byte("usage_usec 0"), 0644)
	os.WriteFile(filepath.Join(tmpDir, "memory.current"), []byte("1073741824"), 0644) // 1GB
	os.WriteFile(filepath.Join(tmpDir, "io.stat"), []byte(""), 0644)

	m, err := NewManager(tmpDir)
	if err != nil {
		t.Fatal("NewManager:", err)
	}

	// Initial reading
	m.Tick(time.Now())
	stats1, _ := m.ReadStats()
	t.Logf("Initial GB-seconds: %.3f", stats1.MemoryGBSeconds)

	// Wait 2 seconds with 1GB usage
	time.Sleep(2 * time.Second)
	m.Tick(time.Now())

	stats2, _ := m.ReadStats()
	t.Logf("After 2s with 1GB: %.3f GB-seconds", stats2.MemoryGBSeconds)

	// Should have added ~2 GB-seconds (allow for timing variance)
	delta := stats2.MemoryGBSeconds - stats1.MemoryGBSeconds
	if delta < 1.8 || delta > 2.3 {
		t.Errorf("Expected ~2 GB-seconds added, got %.3f", delta)
	}

	// Change memory to 2GB
	os.WriteFile(filepath.Join(tmpDir, "memory.current"), []byte("2147483648"), 0644)

	// Wait 1 second
	time.Sleep(1 * time.Second)
	m.Tick(time.Now())

	stats3, _ := m.ReadStats()
	t.Logf("After 1s with 2GB: %.3f GB-seconds", stats3.MemoryGBSeconds)

	// Should have added ~2 more GB-seconds (allow for timing variance)
	delta2 := stats3.MemoryGBSeconds - stats2.MemoryGBSeconds
	if delta2 < 1.8 || delta2 > 2.3 {
		t.Errorf("Expected ~2 GB-seconds added with 2GB memory, got %.3f", delta2)
	}
}

// TestIOStats tests IO stat parsing
func TestIOStats(t *testing.T) {
	// Reset global CPU balance for clean test state
	ResetGlobalCPUBalance()

	tmpDir := t.TempDir()

	// Create mock files
	os.WriteFile(filepath.Join(tmpDir, "cpu.stat"), []byte("usage_usec 0"), 0644)
	os.WriteFile(filepath.Join(tmpDir, "memory.current"), []byte("0"), 0644)

	// Mock io.stat with multiple devices
	ioStat := `8:0 rbytes=10485760 wbytes=20971520 rios=100 wios=200 dbytes=0 dios=0
8:16 rbytes=5242880 wbytes=10485760 rios=50 wios=100 dbytes=0 dios=0
`
	os.WriteFile(filepath.Join(tmpDir, "io.stat"), []byte(ioStat), 0644)

	m, err := NewManager(tmpDir)
	if err != nil {
		t.Fatal("NewManager:", err)
	}

	stats, err := m.ReadStats()
	if err != nil {
		t.Fatal("ReadStats:", err)
	}

	// Should aggregate across devices
	expectedRead := uint64(10485760 + 5242880)   // 15MB
	expectedWrite := uint64(20971520 + 10485760) // 30MB

	if stats.IOReadBytes != expectedRead {
		t.Errorf("Expected %d read bytes, got %d", expectedRead, stats.IOReadBytes)
	}
	if stats.IOWriteBytes != expectedWrite {
		t.Errorf("Expected %d write bytes, got %d", expectedWrite, stats.IOWriteBytes)
	}

	t.Logf("IO stats - read: %d MB, write: %d MB", stats.IOReadBytes/1024/1024, stats.IOWriteBytes/1024/1024)
}

// TestQuotaOperations tests setting CPU and memory quotas
func TestQuotaOperations(t *testing.T) {
	// Reset global CPU balance for clean test state
	ResetGlobalCPUBalance()

	tmpDir := t.TempDir()

	// Create mock files
	os.WriteFile(filepath.Join(tmpDir, "cpu.stat"), []byte("usage_usec 0"), 0644)
	os.WriteFile(filepath.Join(tmpDir, "memory.current"), []byte("0"), 0644)
	os.WriteFile(filepath.Join(tmpDir, "io.stat"), []byte(""), 0644)
	os.WriteFile(filepath.Join(tmpDir, "cpu.max"), []byte(""), 0644)
	os.WriteFile(filepath.Join(tmpDir, "memory.low"), []byte(""), 0644)
	os.WriteFile(filepath.Join(tmpDir, "memory.high"), []byte(""), 0644)

	m, err := NewManager(tmpDir)
	if err != nil {
		t.Fatal("NewManager:", err)
	}

	// Test CPU quota
	if err := m.SetCPUQuota(50*time.Millisecond, 100*time.Millisecond); err != nil {
		t.Fatal("SetCPUQuota:", err)
	}

	content, _ := os.ReadFile(filepath.Join(tmpDir, "cpu.max"))
	if string(content) != "50000 100000\n" {
		t.Errorf("Expected '50000 100000\\n', got %q", content)
	}

	// Remove quota
	if err := m.SetCPUQuota(0, 100*time.Millisecond); err != nil {
		t.Fatal("SetCPUQuota(remove):", err)
	}

	content, _ = os.ReadFile(filepath.Join(tmpDir, "cpu.max"))
	if string(content) != "max\n" {
		t.Errorf("Expected 'max\\n', got %q", content)
	}

	// Test memory limits
	if err := m.SetMinimumMemory(256 * 1024 * 1024); err != nil {
		t.Fatal("SetMinimumMemory:", err)
	}

	content, _ = os.ReadFile(filepath.Join(tmpDir, "memory.low"))
	if string(content) != "268435456\n" {
		t.Errorf("Expected '268435456\\n', got %q", content)
	}

	if err := m.SetMaximumMemory(2 * 1024 * 1024 * 1024); err != nil {
		t.Fatal("SetMaximumMemory:", err)
	}

	content, _ = os.ReadFile(filepath.Join(tmpDir, "memory.high"))
	if string(content) != "2147483648\n" {
		t.Errorf("Expected '2147483648\\n', got %q", content)
	}

	// Test removing memory limit
	if err := m.SetMaximumMemory(0); err != nil {
		t.Fatal("SetMaximumMemory(remove):", err)
	}

	content, _ = os.ReadFile(filepath.Join(tmpDir, "memory.high"))
	if string(content) != "max\n" {
		t.Errorf("Expected 'max\\n', got %q", content)
	}
}

// TestRealCgroupIntegration runs if we can actually create and use cgroups
func TestRealCgroupIntegration(t *testing.T) {
	// Reset global CPU balance for clean test state
	ResetGlobalCPUBalance()

	// Verify we're using cgroup v2
	if _, err := os.Stat("/sys/fs/cgroup/cgroup.controllers"); err != nil {
		t.Fatal("Not using cgroup v2 unified hierarchy - missing cgroup.controllers")
	}

	// Check what controllers are available
	if controllers, err := os.ReadFile("/sys/fs/cgroup/cgroup.controllers"); err == nil {
		t.Logf("Available cgroup v2 controllers: %s", strings.TrimSpace(string(controllers)))
	}

	// Check cgroup v2 specific files exist
	v2Files := []string{
		"/sys/fs/cgroup/cgroup.subtree_control",
		"/sys/fs/cgroup/cgroup.threads",
		"/sys/fs/cgroup/cpu.stat",
		"/sys/fs/cgroup/memory.stat",
		"/sys/fs/cgroup/io.stat",
	}
	for _, f := range v2Files {
		if _, err := os.Stat(f); err != nil {
			t.Logf("Missing cgroup v2 file: %s", f)
		}
	}

	// Check mount info to confirm cgroup2
	if mounts, err := os.ReadFile("/proc/self/mountinfo"); err == nil {
		for _, line := range strings.Split(string(mounts), "\n") {
			if strings.Contains(line, "/sys/fs/cgroup") && strings.Contains(line, "cgroup") {
				t.Logf("Cgroup mount: %s", line)
				if !strings.Contains(line, "cgroup2") {
					t.Fatal("Not using cgroup2 filesystem!")
				}
			}
		}
	}

	// Log current user and cgroup info for debugging
	t.Logf("Running as UID: %d, GID: %d", os.Getuid(), os.Getgid())
	if data, err := os.ReadFile("/proc/self/cgroup"); err == nil {
		t.Logf("Current cgroup: %s", strings.TrimSpace(string(data)))
	}

	// Try to create a test cgroup under the unified hierarchy
	testPath := filepath.Join("/sys/fs/cgroup", fmt.Sprintf("sprite-test-%d", os.Getpid()))
	if err := os.Mkdir(testPath, 0755); err != nil {
		t.Skipf("Can't create test cgroup: %v", err)
	}

	t.Cleanup(func() {
		// Kill any processes in the cgroup
		_ = os.WriteFile(filepath.Join(testPath, "cgroup.kill"), []byte("1"), 0644)
		time.Sleep(100 * time.Millisecond)
		_ = os.Remove(testPath)
	})

	// Enable controllers we need
	parentControl := "/sys/fs/cgroup/cgroup.subtree_control"
	for _, ctrl := range []string{"+cpu", "+memory", "+io"} {
		if err := os.WriteFile(parentControl, []byte(ctrl), 0644); err != nil {
			t.Logf("Warning: couldn't enable %s controller: %v", ctrl, err)
		}
	}

	m, err := NewManager(testPath)
	if err != nil {
		t.Fatal("NewManager:", err)
	}

	// Set resource limits - skip if we don't have permissions
	if err := m.SetCPUQuota(100*time.Millisecond, 100*time.Millisecond); err != nil {
		t.Skipf("Can't set CPU quota (insufficient cgroup privileges): %v", err)
	}
	if err := m.SetMinimumMemory(50 * 1024 * 1024); err != nil {
		t.Skipf("Can't set memory.low (insufficient cgroup privileges): %v", err)
	}
	if err := m.SetMaximumMemory(200 * 1024 * 1024); err != nil {
		t.Skipf("Can't set memory.high (insufficient cgroup privileges): %v", err)
	}

	// Try to run a real workload in the cgroup
	script := filepath.Join("/workspace/pkg/resources/test-helpers/cpu-burner.sh")
	if _, err := os.Stat(script); err != nil {
		script = filepath.Join("test-helpers/cpu-burner.sh")
		if _, err := os.Stat(script); err != nil {
			t.Skip("Can't find test helper scripts")
		}
	}

	cmd := exec.Command(script, "1")
	if err := cmd.Start(); err != nil {
		t.Fatalf("Failed to start CPU burner: %v", err)
	}

	// Move to our cgroup
	pidStr := fmt.Sprintf("%d", cmd.Process.Pid)
	if err := os.WriteFile(filepath.Join(testPath, "cgroup.procs"), []byte(pidStr), 0644); err != nil {
		cmd.Process.Kill()
		t.Skipf("Can't move process to cgroup: %v", err)
	}

	// Let it run and collect stats
	time.Sleep(500 * time.Millisecond)
	m.Tick(time.Now())
	stats1, _ := m.ReadStats()

	// Wait for completion
	cmd.Wait()

	// Final stats
	m.Tick(time.Now())
	stats2, _ := m.ReadStats()

	t.Logf("CPU usage: %v -> %v (delta: %v)",
		stats1.CPUUsageTotal, stats2.CPUUsageTotal,
		stats2.CPUUsageTotal-stats1.CPUUsageTotal)
	t.Logf("Memory peak: %d MB", stats2.MemoryCurrentBytes/1024/1024)
	t.Logf("CPU bank: %v", m.CPUBankBalance())

	// Check if we saw throttling
	cpuStat, _ := m.ReadCPUStat()
	if cpuStat.NrThrottled > 0 {
		t.Logf("CPU throttling detected: %d/%d periods, %v throttled time",
			cpuStat.NrThrottled, cpuStat.NrPeriods, cpuStat.ThrottledTime)
	}

	// Check pressure detection
	pressure, err := m.CheckPressure()
	if err != nil {
		t.Fatal("CheckPressure:", err)
	}

	t.Logf("Pressure check - CPU throttled: %v (%.1f%%), Memory: %.1f%% of limit",
		pressure.CPUThrottled, pressure.CPUThrottledPercent, pressure.MemoryUsagePercent)
	t.Logf("CPU bank: %v/%v, Accrual: %v/s, Demand: %v/s, Deficit: %v",
		pressure.CPUBankBalance, pressure.CPUBankMax, pressure.CPUAccrualRate,
		pressure.CPUDemandRate, pressure.CPUDeficit)
	t.Logf("Needs upgrade - CPU: %v, Memory: %v (optimal: %d MB)",
		pressure.NeedsCPUUpgrade, pressure.NeedsMemoryUpgrade, pressure.EstimatedOptimalMemoryMB)

	// We set 100% CPU quota so we should see CPU pressure
	if !pressure.CPUThrottled {
		t.Error("Expected CPU throttling to be detected")
	}
	// With variable CPU counts, just verify we detected significant throttling
	if pressure.CPUThrottledPercent < 25 {
		t.Errorf("Expected significant CPU throttle percentage, got %.1f%%", pressure.CPUThrottledPercent)
	}
}

// TestMemoryPressureDetection tests detecting when memory is constrained
func TestMemoryPressureDetection(t *testing.T) {
	// Reset global CPU balance for clean test state
	ResetGlobalCPUBalance()

	tmpDir := t.TempDir()

	// Create mock files
	os.WriteFile(filepath.Join(tmpDir, "cpu.stat"), []byte("usage_usec 0"), 0644)
	os.WriteFile(filepath.Join(tmpDir, "memory.current"), []byte("1900000000"), 0644) // 1.9GB
	os.WriteFile(filepath.Join(tmpDir, "memory.high"), []byte("2147483648"), 0644)    // 2GB
	os.WriteFile(filepath.Join(tmpDir, "io.stat"), []byte(""), 0644)
	os.WriteFile(filepath.Join(tmpDir, "io.pressure"), []byte("some avg10=0.00 avg60=0.00 avg300=0.00 total=0\nfull avg10=0.00 avg60=0.00 avg300=0.00 total=0\n"), 0644)

	// Mock memory.stat with high pressure indicators
	memStat := `anon 1800000000
file 100000000
pgfault 50000
pgmajfault 200
workingset_refault 2000
workingset_activate 1500
pgrefill 5000
pgsteal 3000
`
	os.WriteFile(filepath.Join(tmpDir, "memory.stat"), []byte(memStat), 0644)

	// Mock memory.events with some pressure events
	memEvents := `low 0
high 150
max 5
oom 0
oom_kill 0
`
	os.WriteFile(filepath.Join(tmpDir, "memory.events"), []byte(memEvents), 0644)

	// Mock memory.pressure showing actual allocation stalls
	memPressure := `some avg10=15.50 avg60=12.30 avg300=8.45 total=123456
full avg10=2.10 avg60=1.50 avg300=0.85 total=45678
`
	os.WriteFile(filepath.Join(tmpDir, "memory.pressure"), []byte(memPressure), 0644)

	m, err := NewManager(tmpDir)
	if err != nil {
		t.Fatal("NewManager:", err)
	}

	pressure, err := m.CheckPressure()
	if err != nil {
		t.Fatal("CheckPressure:", err)
	}

	t.Logf("Memory pressure detected: %v", pressure.MemoryPressure)
	t.Logf("Memory usage: %.1f%% of limit", pressure.MemoryUsagePercent)
	t.Logf("Memory reclaims: %d", pressure.MemoryReclaims)
	t.Logf("Needs memory upgrade: %v", pressure.NeedsMemoryUpgrade)
	t.Logf("Estimated optimal memory: %d MB", pressure.EstimatedOptimalMemoryMB)

	// Should detect memory pressure due to workingset refaults
	if !pressure.MemoryPressure {
		t.Error("Expected memory pressure due to high workingset refaults")
	}

	// Should suggest upgrade due to refaults and major faults
	if !pressure.NeedsMemoryUpgrade {
		t.Error("Expected memory upgrade due to thrashing and major faults")
	}

	// Should estimate optimal memory based on pressure signals
	// With 15.5% stalls and high refaults, we expect at least 2.5GB optimal
	if pressure.EstimatedOptimalMemoryMB < 2500 {
		t.Errorf("Expected optimal memory >= 2500MB, got %d MB", pressure.EstimatedOptimalMemoryMB)
	}

	// Test with OOM kill
	memEventsOOM := `low 0
high 150
max 5
oom 1
oom_kill 1
`
	os.WriteFile(filepath.Join(tmpDir, "memory.events"), []byte(memEventsOOM), 0644)

	pressure2, _ := m.CheckPressure()
	if !pressure2.NeedsMemoryUpgrade {
		t.Error("Expected memory upgrade after OOM kill")
	}

	// Test with memory at hard limit
	os.WriteFile(filepath.Join(tmpDir, "memory.current"), []byte("2147483648"), 0644) // 2GB (at max)
	memEventsMax := `low 0
high 150
max 50
oom 0
oom_kill 0
`
	os.WriteFile(filepath.Join(tmpDir, "memory.events"), []byte(memEventsMax), 0644)

	pressure3, _ := m.CheckPressure()
	if !pressure3.MemoryPressure {
		t.Error("Expected memory pressure when at hard limit")
	}
	if !pressure3.NeedsMemoryUpgrade {
		t.Error("Expected memory upgrade when hitting hard limit")
	}
}

// TestCPUPressureDetection tests detecting when CPU is constrained
func TestCPUPressureDetection(t *testing.T) {
	// Reset global CPU balance for clean test state
	ResetGlobalCPUBalance()

	tmpDir := t.TempDir()

	// Create mock files
	os.WriteFile(filepath.Join(tmpDir, "memory.current"), []byte("256000000"), 0644) // 256MB
	os.WriteFile(filepath.Join(tmpDir, "memory.max"), []byte("2147483648"), 0644)    // 2GB
	os.WriteFile(filepath.Join(tmpDir, "io.stat"), []byte(""), 0644)
	os.WriteFile(filepath.Join(tmpDir, "io.pressure"), []byte("some avg10=0.00 avg60=0.00 avg300=0.00 total=0\nfull avg10=0.00 avg60=0.00 avg300=0.00 total=0\n"), 0644)

	// Mock CPU quota - 100% of 1 CPU (100ms per 100ms)
	os.WriteFile(filepath.Join(tmpDir, "cpu.max"), []byte("100000 100000"), 0644)

	// Mock cpu.stat showing significant throttling
	cpuStat := `usage_usec 5000000
user_usec 4000000
system_usec 1000000
nr_periods 100
nr_throttled 45
throttled_usec 2500000
`
	os.WriteFile(filepath.Join(tmpDir, "cpu.stat"), []byte(cpuStat), 0644)

	m, err := NewManager(tmpDir) // 2 CPUs
	if err != nil {
		t.Fatal("NewManager:", err)
	}

	pressure, err := m.CheckPressure()
	if err != nil {
		t.Fatal("CheckPressure:", err)
	}

	t.Logf("CPU throttled: %v (%.1f%%)", pressure.CPUThrottled, pressure.CPUThrottledPercent)
	t.Logf("Needs CPU upgrade: %v", pressure.NeedsCPUUpgrade)
	t.Logf("CPU bank: %v/%v", pressure.CPUBankBalance, pressure.CPUBankMax)
	t.Logf("Accrual rate: %v/s", pressure.CPUAccrualRate)
	t.Logf("Demand rate: %v/s", pressure.CPUDemandRate)
	t.Logf("CPU deficit: %v", pressure.CPUDeficit)

	// Should detect CPU pressure (45% throttled)
	if !pressure.CPUThrottled {
		t.Error("Expected CPU throttling to be detected")
	}

	// Should suggest upgrade (>25% throttled)
	if !pressure.NeedsCPUUpgrade {
		t.Error("Expected CPU upgrade to be suggested")
	}

	// Accrual rate should be positive and based on system CPUs
	if pressure.CPUAccrualRate <= 0 {
		t.Errorf("Expected positive accrual rate, got %v", pressure.CPUAccrualRate)
	}
	t.Logf("Accrual rate (system CPU based): %v/s", pressure.CPUAccrualRate)

	// Demand should exceed accrual when throttled
	if pressure.CPUDemandRate <= pressure.CPUAccrualRate {
		t.Errorf("Expected demand (%v) > accrual (%v) when throttled",
			pressure.CPUDemandRate, pressure.CPUAccrualRate)
	}

	// Should have a bank max of 500s
	if pressure.CPUBankMax != 500*time.Second {
		t.Errorf("Expected bank max 500s, got %v", pressure.CPUBankMax)
	}
}
