package resources

import (
	"sync"
	"time"
)

// mockManager implements ResourceManager for testing
type mockManager struct {
	mu sync.Mutex

	// State
	cpuUsage        time.Duration
	memoryUsage     uint64
	memoryGBSeconds float64
	cpuDeficit      time.Duration
	cpuBank         time.Duration

	// Limits (for tracking only - monitor shouldn't set these)
	memoryMin uint64
	memoryMax uint64
	cpuQuota  time.Duration
	cpuPeriod time.Duration

	// Counters
	tickCount      int
	setMemoryCount int
	setCPUCount    int
}

func newMockManager() *mockManager {
	return &mockManager{
		cpuBank:     100 * time.Millisecond,
		memoryUsage: 256 * 1024 * 1024, // 256MB
		memoryMin:   256 * 1024 * 1024,
		memoryMax:   512 * 1024 * 1024,
		cpuQuota:    100 * time.Millisecond,
		cpuPeriod:   100 * time.Millisecond,
	}
}

func (m *mockManager) Tick(now time.Time) error {
	m.mu.Lock()
	defer m.mu.Unlock()

	m.tickCount++

	// Simulate CPU usage
	m.cpuUsage += 10 * time.Millisecond

	// Simulate memory GB-seconds accumulation
	m.memoryGBSeconds += float64(m.memoryUsage) / 1e9 * 0.1 // 100ms tick

	return nil
}

func (m *mockManager) ReadStats() (Stats, error) {
	m.mu.Lock()
	defer m.mu.Unlock()

	return Stats{
		CPUUsageTotal:      m.cpuUsage,
		MemoryCurrentBytes: m.memoryUsage,
		MemoryGBSeconds:    m.memoryGBSeconds,
		IOReadBytes:        0,
		IOWriteBytes:       0,
		IOReadGB:           0,
		IOWriteGB:          0,
		IOReadOps:          0,
		IOWriteOps:         0,
		CPUDeficit:         m.cpuDeficit,
	}, nil
}

func (m *mockManager) CPUBankBalance() time.Duration {
	m.mu.Lock()
	defer m.mu.Unlock()

	return m.cpuBank
}

func (m *mockManager) CPUDeficit() time.Duration {
	m.mu.Lock()
	defer m.mu.Unlock()

	return m.cpuDeficit
}

func (m *mockManager) getTickCount() int {
	m.mu.Lock()
	defer m.mu.Unlock()

	return m.tickCount
}

func (m *mockManager) getSetMemoryCount() int {
	m.mu.Lock()
	defer m.mu.Unlock()

	return m.setMemoryCount
}

func (m *mockManager) getSetCPUCount() int {
	m.mu.Lock()
	defer m.mu.Unlock()

	return m.setCPUCount
}
