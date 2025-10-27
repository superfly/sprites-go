package resources

import (
	"encoding/json"
	"sync"
	"testing"
	"time"
)

func TestMonitorBasic(t *testing.T) {
	mock := newMockManager()

	var metrics []Metrics
	opts := MonitorOptions{
		Interval: 50 * time.Millisecond,
		Type:     "test",
		MetricsCallback: func(m interface{}) {
			if metric, ok := m.(Metrics); ok {
				metrics = append(metrics, metric)
			}
		},
	}

	mon := NewMonitorWithManager(mock, opts)
	time.Sleep(200 * time.Millisecond)
	mon.Stop()

	t.Logf("Collected %d metric samples, ticked %d times", len(metrics), mock.getTickCount())

	// Should emit metrics every interval
	if len(metrics) < 2 {
		t.Errorf("Expected at least 2 emissions, got %d", len(metrics))
	}

	// Check metrics structure
	if len(metrics) > 0 {
		m := metrics[0]
		if m.Type != "test" {
			t.Errorf("Expected type 'test', got %s", m.Type)
		}
		if m.CPUSecondsTotal < 0 {
			t.Errorf("Expected non-negative CPUSecondsTotal, got %.3f", m.CPUSecondsTotal)
		}
		if m.MemoryCurrentMB == 0 {
			t.Error("Expected non-zero MemoryCurrentMB")
		}
	}
}

func TestMonitorJSON(t *testing.T) {
	m := Metrics{
		Type:                  "test",
		Timestamp:             "2025-10-27T15:04:05Z",
		CPUSeconds:            12.3,
		CPUSecondsTotal:       123.456,
		MemorySeconds:         78.9,
		MemorySecondsTotal:    789.012,
		CPUDeficit:            0.05,
		CPUDeficitTotal:       0.5,
		BillableCPUSeconds:    15.0,
		BillableMemorySeconds: 80.0,
		MemoryCurrentMB:       512,
	}

	data, err := json.Marshal(m)
	if err != nil {
		t.Fatal("Marshal:", err)
	}

	t.Logf("JSON: %s", string(data))

	// Verify underscore case with _s suffix
	var decoded map[string]interface{}
	if err := json.Unmarshal(data, &decoded); err != nil {
		t.Fatal("Unmarshal:", err)
	}

	expectedKeys := []string{
		"type",
		"timestamp",
		"cpu_s",
		"cpu_s_total",
		"runtime_s",
		"memory_s",
		"memory_s_total",
		"cpu_deficit_s",
		"cpu_deficit_s_total",
		"billable_cpu_s",
		"billable_mem_s",
		"io_read_gb",
		"io_write_gb",
		"iops_read",
		"iops_write",
		"io_read_gb_total",
		"io_write_gb_total",
		"iops_read_total",
		"iops_write_total",
		"memory_current_mb",
	}

	for _, key := range expectedKeys {
		if _, ok := decoded[key]; !ok {
			t.Errorf("Expected key %s in JSON", key)
		}
	}
}

func TestVMMetricsJSON(t *testing.T) {
	vm := VMMetrics{
		Type:            "vm",
		CPUBalance:      45.2,
		CPUDeficitTotal: 0.5,
	}

	data, err := json.Marshal(vm)
	if err != nil {
		t.Fatal("Marshal:", err)
	}

	t.Logf("JSON: %s", string(data))

	// Verify underscore case with _s suffix
	var decoded map[string]interface{}
	if err := json.Unmarshal(data, &decoded); err != nil {
		t.Fatal("Unmarshal:", err)
	}

	expectedKeys := []string{
		"type",
		"cpu_balance_s",
		"cpu_deficit_s_total",
	}

	for _, key := range expectedKeys {
		if _, ok := decoded[key]; !ok {
			t.Errorf("Expected key %s in JSON", key)
		}
	}
}

func TestMonitorFlush(t *testing.T) {
	mock := newMockManager()

	var metrics []Metrics
	var mu sync.Mutex

	opts := MonitorOptions{
		Interval: 1 * time.Hour, // No automatic flushes
		Type:     "test",
		MetricsCallback: func(m interface{}) {
			mu.Lock()
			defer mu.Unlock()
			if metric, ok := m.(Metrics); ok {
				metrics = append(metrics, metric)
			}
		},
	}

	mon := NewMonitorWithManager(mock, opts)
	defer mon.Stop()

	// Manually tick
	mon.Manager().Tick(time.Now())
	time.Sleep(10 * time.Millisecond)
	mon.Manager().Tick(time.Now())

	// Manual flush
	mon.Flush()

	mu.Lock()
	count1 := len(metrics)
	first := metrics[0]
	mu.Unlock()

	if count1 != 1 {
		t.Errorf("Expected 1 flush, got %d", count1)
	}

	t.Logf("First flush: CPU=%.3fs (delta=%.3fs), MemGBS=%.3f (delta=%.3f)",
		first.CPUSecondsTotal, first.CPUSeconds, first.MemorySecondsTotal, first.MemorySeconds)

	// Tick more
	mon.Manager().Tick(time.Now())
	time.Sleep(10 * time.Millisecond)
	mon.Manager().Tick(time.Now())

	// Second flush - should have new values
	mon.Flush()

	mu.Lock()
	count2 := len(metrics)
	second := metrics[1]
	mu.Unlock()

	if count2 != 2 {
		t.Errorf("Expected 2 flushes, got %d", count2)
	}

	t.Logf("Second flush: CPU=%.3fs (delta=%.3fs), MemGBS=%.3f (delta=%.3f)",
		second.CPUSecondsTotal, second.CPUSeconds, second.MemorySecondsTotal, second.MemorySeconds)

	// Totals should be cumulative (second >= first)
	if first.CPUSecondsTotal <= 0 {
		t.Error("Expected positive CPU total in first flush")
	}
	if second.CPUSecondsTotal < first.CPUSecondsTotal {
		t.Error("Expected second CPU total to be >= first (cumulative)")
	}

	// Deltas should both be positive (measuring activity)
	if first.CPUSeconds <= 0 {
		t.Error("Expected positive CPU delta in first flush")
	}
	if second.CPUSeconds <= 0 {
		t.Error("Expected positive CPU delta in second flush")
	}
}

func TestMonitorNoLimitSetting(t *testing.T) {
	mock := newMockManager()

	var lastMetrics Metrics
	opts := MonitorOptions{
		Interval: 10 * time.Millisecond,
		Type:     "test",
		MetricsCallback: func(m interface{}) {
			if metric, ok := m.(Metrics); ok {
				lastMetrics = metric
			}
		},
	}

	mon := NewMonitorWithManager(mock, opts)
	time.Sleep(50 * time.Millisecond)
	mon.Stop()

	t.Logf("Accounting only: Current Memory=%dMB", lastMetrics.MemoryCurrentMB)

	// Monitor should report accounting but NOT set any limits
	// The mock manager tracks limit setting calls - verify none were made
	if mock.getSetMemoryCount() > 0 {
		t.Errorf("Monitor should not set memory limits (accounting only), but got %d calls",
			mock.getSetMemoryCount())
	}
	if mock.getSetCPUCount() > 0 {
		t.Errorf("Monitor should not set CPU limits (accounting only), but got %d calls",
			mock.getSetCPUCount())
	}

	// Verify we're reporting the metrics
	if lastMetrics.MemoryCurrentMB == 0 {
		t.Error("Expected non-zero current memory")
	}
}

func TestMonitorCounterReset(t *testing.T) {
	mock := newMockManager()

	var metrics []Metrics
	opts := MonitorOptions{
		Interval: 50 * time.Millisecond,
		Type:     "test",
		MetricsCallback: func(m interface{}) {
			if metric, ok := m.(Metrics); ok {
				metrics = append(metrics, metric)
			}
		},
	}

	mon := NewMonitorWithManager(mock, opts)
	time.Sleep(200 * time.Millisecond)
	mon.Stop()

	if len(metrics) < 2 {
		t.Fatalf("Expected at least 2 flushes, got %d", len(metrics))
	}

	// Check that deltas are reasonable and totals are cumulative
	var lastCPUTotal float64
	for i, m := range metrics {
		t.Logf("Flush %d: CPU=%.3fs (total=%.3fs), MemGBS=%.3f (total=%.3f)",
			i, m.CPUSeconds, m.CPUSecondsTotal, m.MemorySeconds, m.MemorySecondsTotal)

		// Deltas should be relatively small per interval (not cumulative)
		if m.CPUSeconds > 0.1 {
			t.Errorf("Flush %d: CPU delta too high (%.3fs), should reset between flushes", i, m.CPUSeconds)
		}

		// Totals should always increase
		if m.CPUSecondsTotal < lastCPUTotal {
			t.Errorf("Flush %d: CPU total decreased (%.3fs < %.3fs), should be cumulative", i, m.CPUSecondsTotal, lastCPUTotal)
		}
		lastCPUTotal = m.CPUSecondsTotal
	}
}

func TestMonitorRuntimeTracking(t *testing.T) {
	mock := newMockManager()

	var metrics []Metrics
	var mu sync.Mutex

	opts := MonitorOptions{
		Interval: 50 * time.Millisecond,
		Type:     "test",
		MetricsCallback: func(m interface{}) {
			mu.Lock()
			defer mu.Unlock()
			if metric, ok := m.(Metrics); ok {
				metrics = append(metrics, metric)
			}
		},
	}

	mon := NewMonitorWithManager(mock, opts)

	// Let it run for ~150ms
	time.Sleep(150 * time.Millisecond)
	mon.Stop()

	mu.Lock()
	defer mu.Unlock()

	if len(metrics) < 2 {
		t.Fatalf("Expected at least 2 flushes, got %d", len(metrics))
	}

	// Runtime should be monotonically increasing
	var lastRuntime float64
	for i, m := range metrics {
		t.Logf("Flush %d: RuntimeSeconds=%.3fs", i, m.RuntimeSeconds)

		if m.RuntimeSeconds < lastRuntime {
			t.Errorf("Flush %d: Runtime decreased (%.3fs < %.3fs), should be monotonic", i, m.RuntimeSeconds, lastRuntime)
		}

		// Runtime should be positive after first flush
		if i > 0 && m.RuntimeSeconds <= 0 {
			t.Errorf("Flush %d: Expected positive runtime, got %.3fs", i, m.RuntimeSeconds)
		}

		lastRuntime = m.RuntimeSeconds
	}

	// Final runtime should be approximately the time we ran (~150ms)
	finalRuntime := metrics[len(metrics)-1].RuntimeSeconds
	expectedMin := 0.100 // 100ms minimum
	expectedMax := 0.300 // 300ms maximum (generous upper bound)

	if finalRuntime < expectedMin || finalRuntime > expectedMax {
		t.Errorf("Expected runtime between %.3fs and %.3fs, got %.3fs", expectedMin, expectedMax, finalRuntime)
	}
}

func TestMonitorRuntimeExcludesSuspendedTime(t *testing.T) {
	mock := newMockManager()

	var metrics []Metrics
	var mu sync.Mutex

	opts := MonitorOptions{
		Interval: 50 * time.Millisecond,
		Type:     "test",
		MetricsCallback: func(m interface{}) {
			mu.Lock()
			defer mu.Unlock()
			if metric, ok := m.(Metrics); ok {
				metrics = append(metrics, metric)
			}
		},
	}

	mon := NewMonitorWithManager(mock, opts)

	// Run for 100ms
	time.Sleep(100 * time.Millisecond)

	mu.Lock()
	preCount := len(metrics)
	var runtimeBeforePause float64
	if preCount > 0 {
		runtimeBeforePause = metrics[preCount-1].RuntimeSeconds
	}
	mu.Unlock()

	t.Logf("Before pause: %d metrics, runtime=%.3fs", preCount, runtimeBeforePause)

	// Pause the monitor
	mon.Pause()

	// Wait while paused (this time should NOT be counted)
	suspendDuration := 200 * time.Millisecond
	time.Sleep(suspendDuration)

	// Resume
	mon.Resume()

	// Run for another 100ms
	time.Sleep(100 * time.Millisecond)
	mon.Stop()

	mu.Lock()
	defer mu.Unlock()

	if len(metrics) < 2 {
		t.Fatalf("Expected at least 2 flushes, got %d", len(metrics))
	}

	finalRuntime := metrics[len(metrics)-1].RuntimeSeconds
	t.Logf("After resume: %d metrics, final runtime=%.3fs", len(metrics), finalRuntime)

	// Runtime should be roughly 200ms (100ms before pause + 100ms after resume)
	// It should NOT include the 200ms suspend time
	expectedMin := 0.150 // 150ms minimum
	expectedMax := 0.350 // 350ms maximum (generous)

	// The key assertion: suspended time should NOT be counted
	maxIfSuspendCounted := 0.500 // Would be ~500ms if suspend time was counted

	if finalRuntime > maxIfSuspendCounted {
		t.Errorf("Runtime too high (%.3fs), appears to include suspended time", finalRuntime)
	}

	if finalRuntime < expectedMin {
		t.Errorf("Runtime too low (%.3fs), expected at least %.3fs", finalRuntime, expectedMin)
	}

	if finalRuntime > expectedMax {
		t.Errorf("Runtime too high (%.3fs), expected at most %.3fs", finalRuntime, expectedMax)
	}

	t.Logf("✓ Runtime correctly excluded ~%.0fms of suspended time", suspendDuration.Seconds()*1000)
}

func TestMonitorRuntimeMultiplePauseResume(t *testing.T) {
	mock := newMockManager()

	var metrics []Metrics
	var mu sync.Mutex

	opts := MonitorOptions{
		Interval: 30 * time.Millisecond,
		Type:     "test",
		MetricsCallback: func(m interface{}) {
			mu.Lock()
			defer mu.Unlock()
			if metric, ok := m.(Metrics); ok {
				metrics = append(metrics, metric)
			}
		},
	}

	mon := NewMonitorWithManager(mock, opts)

	// Run, pause, resume multiple times
	activeTime := 50 * time.Millisecond
	suspendTime := 100 * time.Millisecond
	cycles := 3

	for i := 0; i < cycles; i++ {
		time.Sleep(activeTime)
		mon.Pause()
		time.Sleep(suspendTime)
		mon.Resume()
	}

	// Final active period
	time.Sleep(activeTime)
	mon.Stop()

	mu.Lock()
	defer mu.Unlock()

	if len(metrics) < 2 {
		t.Fatalf("Expected at least 2 flushes, got %d", len(metrics))
	}

	finalRuntime := metrics[len(metrics)-1].RuntimeSeconds
	t.Logf("After %d pause/resume cycles: final runtime=%.3fs", cycles, finalRuntime)

	// Total active time should be roughly (cycles + 1) * activeTime = 200ms
	totalActiveTime := float64(cycles+1) * activeTime.Seconds()
	expectedMin := totalActiveTime * 0.5 // 50% of expected (generous for timing)
	expectedMax := totalActiveTime * 2.0 // 200% of expected

	// Key assertion: should NOT include the 300ms of total suspend time
	totalSuspendTime := float64(cycles) * suspendTime.Seconds()
	maxIfAllCounted := totalActiveTime + totalSuspendTime

	if finalRuntime > maxIfAllCounted*0.9 {
		t.Errorf("Runtime too high (%.3fs), appears to include suspended time", finalRuntime)
	}

	if finalRuntime < expectedMin {
		t.Errorf("Runtime too low (%.3fs), expected at least %.3fs", finalRuntime, expectedMin)
	}

	if finalRuntime > expectedMax {
		t.Errorf("Runtime too high (%.3fs), expected at most %.3fs", finalRuntime, expectedMax)
	}

	t.Logf("✓ Runtime correctly excluded ~%.0fms of suspended time across %d cycles",
		totalSuspendTime*1000, cycles)
}

func TestCalculateBillableMetrics(t *testing.T) {
	tests := []struct {
		name           string
		runtimeDelta   float64
		cpuUsed        float64
		memoryUsed     float64
		expectedCPU    float64
		expectedMemory float64
	}{
		{
			name:           "actual usage exceeds minimums",
			runtimeDelta:   1.0,   // 1 second
			cpuUsed:        0.500, // 500ms CPU (50%)
			memoryUsed:     1.0,   // 1 GB-second
			expectedCPU:    0.500, // actual usage
			expectedMemory: 1.0,   // actual usage
		},
		{
			name:           "actual usage below minimums",
			runtimeDelta:   1.0,    // 1 second
			cpuUsed:        0.050,  // 50ms CPU (5%)
			memoryUsed:     0.100,  // 100MB-seconds (0.1 GB-s)
			expectedCPU:    0.0625, // minimum 6.25%
			expectedMemory: 0.250,  // minimum 250MB
		},
		{
			name:           "zero usage applies minimums",
			runtimeDelta:   1.0, // 1 second
			cpuUsed:        0.0,
			memoryUsed:     0.0,
			expectedCPU:    0.0625, // minimum 6.25%
			expectedMemory: 0.250,  // minimum 250MB
		},
		{
			name:           "minimums scale with runtime",
			runtimeDelta:   2.0,   // 2 seconds
			cpuUsed:        0.050, // 50ms CPU
			memoryUsed:     0.100, // 100MB-seconds
			expectedCPU:    0.125, // 2 * 0.0625
			expectedMemory: 0.500, // 2 * 0.250
		},
		{
			name:           "mixed - CPU below minimum, memory above",
			runtimeDelta:   1.0,
			cpuUsed:        0.030,  // 30ms CPU (below 6.25%)
			memoryUsed:     0.500,  // 500MB-seconds (above 250MB)
			expectedCPU:    0.0625, // minimum
			expectedMemory: 0.500,  // actual
		},
		{
			name:           "mixed - CPU above minimum, memory below",
			runtimeDelta:   1.0,
			cpuUsed:        0.200, // 200ms CPU (above 6.25%)
			memoryUsed:     0.100, // 100MB-seconds (below 250MB)
			expectedCPU:    0.200, // actual
			expectedMemory: 0.250, // minimum
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cpu, mem := calculateBillableMetrics(tt.runtimeDelta, tt.cpuUsed, tt.memoryUsed)

			if cpu != tt.expectedCPU {
				t.Errorf("CPU: expected %.4f, got %.4f", tt.expectedCPU, cpu)
			}
			if mem != tt.expectedMemory {
				t.Errorf("Memory: expected %.4f, got %.4f", tt.expectedMemory, mem)
			}

			t.Logf("Runtime: %.1fs, Used: CPU=%.3fs MEM=%.3fGB-s → Billable: CPU=%.4fs MEM=%.3fGB-s",
				tt.runtimeDelta, tt.cpuUsed, tt.memoryUsed, cpu, mem)
		})
	}
}

func TestMonitorTimestampIsUTC(t *testing.T) {
	mock := newMockManager()

	var metrics []Metrics
	var mu sync.Mutex

	opts := MonitorOptions{
		Interval: 50 * time.Millisecond,
		Type:     "test",
		MetricsCallback: func(m interface{}) {
			mu.Lock()
			defer mu.Unlock()
			if metric, ok := m.(Metrics); ok {
				metrics = append(metrics, metric)
			}
		},
	}

	mon := NewMonitorWithManager(mock, opts)
	time.Sleep(100 * time.Millisecond)
	mon.Stop()

	mu.Lock()
	defer mu.Unlock()

	if len(metrics) == 0 {
		t.Fatal("Expected at least 1 metric emission")
	}

	for i, m := range metrics {
		// Verify timestamp is not empty
		if m.Timestamp == "" {
			t.Errorf("Metric %d: timestamp is empty", i)
			continue
		}

		// Parse the timestamp
		ts, err := time.Parse(time.RFC3339, m.Timestamp)
		if err != nil {
			t.Errorf("Metric %d: failed to parse timestamp %q: %v", i, m.Timestamp, err)
			continue
		}

		// Verify it's in UTC (zone name should be "UTC")
		if ts.Location() != time.UTC {
			t.Errorf("Metric %d: timestamp %q is not in UTC, got zone: %v", i, m.Timestamp, ts.Location())
		}

		// Verify the timestamp string ends with 'Z' (UTC indicator in RFC3339)
		if m.Timestamp[len(m.Timestamp)-1] != 'Z' {
			t.Errorf("Metric %d: timestamp %q does not end with 'Z' (UTC indicator)", i, m.Timestamp)
		}

		// Verify timestamp is recent (within last minute)
		now := time.Now().UTC()
		age := now.Sub(ts)
		if age < 0 || age > time.Minute {
			t.Errorf("Metric %d: timestamp %q is not recent (age: %v)", i, m.Timestamp, age)
		}

		t.Logf("Metric %d: timestamp=%s (UTC, age: %v)", i, m.Timestamp, age)
	}
}
