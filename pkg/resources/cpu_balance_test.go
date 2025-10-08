package resources

import (
	"os"
	"path/filepath"
	"testing"
	"time"
)

// TestMultipleManagersDoNotCorruptGlobalCPUBalance verifies that creating
// multiple managers doesn't overwrite the global CPU balance state.
func TestMultipleManagersDoNotCorruptGlobalCPUBalance(t *testing.T) {
	ResetGlobalCPUBalance()

	// Create first manager with some CPU usage
	tmpDir1 := t.TempDir()
	os.WriteFile(filepath.Join(tmpDir1, "cpu.stat"), []byte(`usage_usec 1000000
user_usec 800000
system_usec 200000
nr_periods 10
nr_throttled 2
throttled_usec 100000
`), 0644)
	os.WriteFile(filepath.Join(tmpDir1, "memory.current"), []byte("100000000"), 0644)
	os.WriteFile(filepath.Join(tmpDir1, "io.stat"), []byte(""), 0644)

	mgr1, err := NewManager(tmpDir1)
	if err != nil {
		t.Fatal("NewManager 1:", err)
	}

	// Tick the first manager to update global balance
	mgr1.Tick(time.Now())
	time.Sleep(100 * time.Millisecond)

	// Get the global balance after first manager
	cb := GetCPUBalance()
	balanceAfterFirst := cb.Balance()
	lastCPUAfterFirst := cb.lastCPUUsage.Load()

	t.Logf("Balance after first manager: %v", balanceAfterFirst)
	t.Logf("LastCPUUsage after first manager: %d ns", lastCPUAfterFirst)

	// Create second manager with different CPU usage
	tmpDir2 := t.TempDir()
	os.WriteFile(filepath.Join(tmpDir2, "cpu.stat"), []byte(`usage_usec 5000000
user_usec 4000000
system_usec 1000000
nr_periods 20
nr_throttled 5
throttled_usec 250000
`), 0644)
	os.WriteFile(filepath.Join(tmpDir2, "memory.current"), []byte("200000000"), 0644)
	os.WriteFile(filepath.Join(tmpDir2, "io.stat"), []byte(""), 0644)

	_, err = NewManager(tmpDir2)
	if err != nil {
		t.Fatal("NewManager 2:", err)
	}

	// Check that global balance wasn't corrupted by second manager creation
	balanceAfterSecond := cb.Balance()
	lastCPUAfterSecond := cb.lastCPUUsage.Load()

	t.Logf("Balance after second manager: %v", balanceAfterSecond)
	t.Logf("LastCPUUsage after second manager: %d ns", lastCPUAfterSecond)

	// The balance should not have been reset by the second manager creation.
	// It should be the same or have increased (from time accrual), but definitely
	// not corrupted by the second manager's CPU usage value.
	if balanceAfterSecond < balanceAfterFirst {
		t.Errorf("Global balance decreased after creating second manager: %v -> %v",
			balanceAfterFirst, balanceAfterSecond)
	}

	// The lastCPUUsage should not have been overwritten with the second manager's
	// individual cgroup usage (5000000000 ns). It should remain close to what
	// the first manager set it to (1000000000 ns), unless a tick happened.
	expectedCPU := time.Duration(1000000) * time.Microsecond
	actualCPU := time.Duration(lastCPUAfterSecond)

	// Allow for the case where skipGlobalCPUBalance is false and the first manager
	// updated it, but the second manager creation should NOT have changed it.
	// The actual value should be close to the first manager's value.
	if actualCPU > expectedCPU*2 {
		t.Errorf("Global lastCPUUsage was corrupted by second manager creation: expected ~%v, got %v",
			expectedCPU, actualCPU)
	}
}

// TestMonitorGroupCPUAggregation verifies that MonitorGroup correctly aggregates
// CPU usage from multiple managers without corruption.
func TestMonitorGroupCPUAggregation(t *testing.T) {
	ResetGlobalCPUBalance()

	// Create test cgroups
	tmpDir1 := t.TempDir()
	tmpDir2 := t.TempDir()

	// Manager 1: 1 second of CPU usage
	os.WriteFile(filepath.Join(tmpDir1, "cpu.stat"), []byte(`usage_usec 1000000
user_usec 800000
system_usec 200000
nr_periods 10
nr_throttled 0
throttled_usec 0
`), 0644)
	os.WriteFile(filepath.Join(tmpDir1, "memory.current"), []byte("100000000"), 0644)
	os.WriteFile(filepath.Join(tmpDir1, "io.stat"), []byte(""), 0644)

	// Manager 2: 2 seconds of CPU usage
	os.WriteFile(filepath.Join(tmpDir2, "cpu.stat"), []byte(`usage_usec 2000000
user_usec 1600000
system_usec 400000
nr_periods 20
nr_throttled 0
throttled_usec 0
`), 0644)
	os.WriteFile(filepath.Join(tmpDir2, "memory.current"), []byte("200000000"), 0644)
	os.WriteFile(filepath.Join(tmpDir2, "io.stat"), []byte(""), 0644)

	// Create monitor group
	mg, err := NewMonitorGroup(MonitorGroupOptions{
		Cgroups: []struct {
			Path string
			Type string
		}{
			{Path: tmpDir1, Type: "cgroup1"},
			{Path: tmpDir2, Type: "cgroup2"},
		},
		Interval: 100 * time.Millisecond,
	})
	if err != nil {
		t.Fatal("NewMonitorGroup:", err)
	}
	if mg == nil {
		t.Fatal("NewMonitorGroup returned nil without error")
	}
	defer mg.Stop()

	// Verify that individual managers have skipGlobalCPUBalance set
	for _, mgr := range mg.managers {
		if !mgr.skipGlobalCPUBalance {
			t.Error("MonitorGroup manager should have skipGlobalCPUBalance=true")
		}
	}

	// Trigger a CPU balance update
	mg.tickCPUBalance(time.Now())

	// The global balance should now have the aggregated CPU usage (3 seconds total)
	cb := GetCPUBalance()
	lastCPU := time.Duration(cb.lastCPUUsage.Load())
	expectedTotal := time.Duration(3000000) * time.Microsecond // 1s + 2s

	if lastCPU != expectedTotal {
		t.Errorf("Global CPU balance should have aggregated usage: expected %v, got %v",
			expectedTotal, lastCPU)
	}

	t.Logf("Successfully aggregated CPU usage: %v", lastCPU)
}

