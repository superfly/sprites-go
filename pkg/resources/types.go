package resources

import "time"

// Stats captures rolling usage since the Manager was created or Reset was called.
type Stats struct {
	// CPUUsageTotal is the cgroup's cumulative CPU time consumed (since kernel boot),
	// as reported by cpu.stat usage_usec.
	CPUUsageTotal time.Duration

	// MemoryCurrentBytes is the current memory usage of the cgroup.
	MemoryCurrentBytes uint64

	// MemoryGBSeconds is the integral of memory usage over time, measured in GB-seconds,
	// accumulated by the Manager's tracker between successive Tick calls.
	MemoryGBSeconds float64

	// IOReadBytes is the current cumulative read bytes from io.stat.
	IOReadBytes uint64

	// IOWriteBytes is the current cumulative write bytes from io.stat.
	IOWriteBytes uint64

	// IOReadGB is the accumulated read gigabytes since manager creation.
	IOReadGB float64

	// IOWriteGB is the accumulated write gigabytes since manager creation.
	IOWriteGB float64

	// IOReadOps is the accumulated read operations count.
	IOReadOps uint64

	// IOWriteOps is the accumulated write operations count.
	IOWriteOps uint64

	// CPUDeficit is the accumulated CPU time that processes wanted but couldn't get even with banking.
	// This grows when the bank is exhausted and processes are still being throttled.
	CPUDeficit time.Duration
}

// CPUStat contains parsed values from cpu.stat (cgroup v2).
type CPUStat struct {
	UsageTotal    time.Duration // usage_usec
	User          time.Duration // user_usec
	System        time.Duration // system_usec
	NrPeriods     uint64        // nr_periods
	NrThrottled   uint64        // nr_throttled
	ThrottledTime time.Duration // throttled_usec
}

// MemoryStat contains parsed values from memory.stat (cgroup v2).
type MemoryStat struct {
	Anon                  uint64 // anon
	File                  uint64 // file
	KernelStack           uint64 // kernel_stack
	Slab                  uint64 // slab
	Sock                  uint64 // sock
	Shmem                 uint64 // shmem
	FileMapped            uint64 // file_mapped
	FileDirty             uint64 // file_dirty
	FileWriteback         uint64 // file_writeback
	AnonThp               uint64 // anon_thp
	InactiveAnon          uint64 // inactive_anon
	ActiveAnon            uint64 // active_anon
	InactiveFile          uint64 // inactive_file
	ActiveFile            uint64 // active_file
	Unevictable           uint64 // unevictable
	SlabReclaimable       uint64 // slab_reclaimable
	SlabUnreclaimable     uint64 // slab_unreclaimable
	Pgfault               uint64 // pgfault
	Pgmajfault            uint64 // pgmajfault
	WorkingsetRefault     uint64 // workingset_refault
	WorkingsetActivate    uint64 // workingset_activate
	WorkingsetNodereclaim uint64 // workingset_nodereclaim
	Pgrefill              uint64 // pgrefill
	Pgscan                uint64 // pgscan
	Pgsteal               uint64 // pgsteal
	Pgactivate            uint64 // pgactivate
	Pgdeactivate          uint64 // pgdeactivate
	Pglazyfree            uint64 // pglazyfree
	Pglazyfreed           uint64 // pglazyfreed
	ThpFaultAlloc         uint64 // thp_fault_alloc
	ThpCollapseAlloc      uint64 // thp_collapse_alloc
}

// ResourcePressure indicates when resources are constrained
type ResourcePressure struct {
	// CPU pressure - true if being throttled significantly
	CPUThrottled bool
	// Percentage of time being throttled (0-100)
	CPUThrottledPercent float64

	// CPU bank balance (how much CPU time we have saved up)
	CPUBankBalance time.Duration
	// Maximum CPU bank capacity
	CPUBankMax time.Duration
	// Rate at which we're accruing CPU quota
	CPUAccrualRate time.Duration // per second
	// Rate at which CPU is being consumed when not throttled
	CPUDemandRate time.Duration // per second
	// Deficit: how much CPU time we would need but can't get (accumulates when throttled)
	CPUDeficit time.Duration

	// Memory pressure - true if approaching limit
	MemoryPressure bool
	// Current memory usage as percentage of max (0-100)
	MemoryUsagePercent float64
	// Number of times we hit the memory limit and had to reclaim
	MemoryReclaims uint64

	// Estimated memory needed for optimal performance (0 if no estimate)
	EstimatedOptimalMemoryMB uint64

	// IO pressure - true if experiencing IO delays
	IOPressure bool
	// IO wait time from pressure files
	IOWaitPercent float64

	// Suggestion for scaling
	NeedsCPUUpgrade    bool
	NeedsMemoryUpgrade bool
	NeedsIOUpgrade     bool
}

// PressureStall contains parsed values from pressure files (cgroup v2)
type PressureStall struct {
	Some struct {
		Avg10  float64
		Avg60  float64
		Avg300 float64
		Total  uint64
	}
	Full struct {
		Avg10  float64
		Avg60  float64
		Avg300 float64
		Total  uint64
	}
}
