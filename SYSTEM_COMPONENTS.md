# System Components Analysis

## Critical Design Principles

1. **New() does NO setup** - only initializes struct, all setup in Start()
2. **Start() follows STRICT internal ordering** - each step MUST complete before next
3. **Start() ERRORS if already started** - NOT idempotent, returns error to catch bugs
4. **Stop() IS idempotent** - can be called multiple times safely
5. **Components are restartable** - Start() → Stop() → Start() works
6. **Stop() reverses startup order** - cleanup in reverse
7. **No mutex for simple flags** - plain bool is sufficient, document expected usage
8. **Verify checks SYSTEM state** - not internal flags, checks filesystem/processes/mounts
9. **Resources tracked on struct** - []ExternalResource populated during startup
10. **ExternalResource.VerifyCleanedUp** - each resource verifies its own cleanup

## Component Dependency Graph

```
Startup Order (Top to Bottom):
┌─────────────────────────────────────────┐
│  Utilities                               │
│  - Reaper                                │
│  - AdminChannel                          │
│  - ResourceMonitor                       │
└─────────────────────────────────────────┘
              ↓
┌─────────────────────────────────────────┐
│  Network Services                        │
│  - APIServer                             │
│  - SocketServer                          │
└─────────────────────────────────────────┘
              ↓
┌─────────────────────────────────────────┐
│  pkg/db (Database Manager)               │
│  External Resources:                     │
│  - Litestream subprocess                 │
│  - S3 lease (via Leaser)                 │
│  - Local etag file                       │
│  - Database file handles                 │
└─────────────────────────────────────────┘
              ↓
┌─────────────────────────────────────────┐
│  pkg/juicefs (JuiceFS Manager)           │
│  External Resources:                     │
│  - JuiceFS mount daemon process          │
│  - Mount point in /proc/mounts           │
│  - Cache directory with files            │
│  - Metadata database (managed by db)     │
└─────────────────────────────────────────┘
              ↓
┌─────────────────────────────────────────┐
│  pkg/overlay (Overlay Manager)           │
│  External Resources:                     │
│  - Loop devices (/dev/loopX)             │
│  - Ext4 mount on loop device             │
│  - OverlayFS mount                       │
│  - Checkpoint loop devices + mounts      │
│  - Image file (on JuiceFS)               │
└─────────────────────────────────────────┘
              ↓
┌─────────────────────────────────────────┐
│  Container Process                       │
│  - User's main process in namespace      │
└─────────────────────────────────────────┘
              ↓
┌─────────────────────────────────────────┐
│  pkg/services (Services Manager)         │
│  External Resources:                     │
│  - Service subprocess PIDs               │
│  - Service database file                 │
│  - Service log files                     │
└─────────────────────────────────────────┘
              ↓
┌─────────────────────────────────────────┐
│  ActivityMonitor                         │
└─────────────────────────────────────────┘

Shutdown Order: REVERSE of above
```

## Current State vs. Target State

### pkg/leaser (S3 Lease Manager) ✅ COMPLETE

**Implemented:**
```go
type Leaser struct {
    stopCh               chan struct{}
    stoppedCh            chan struct{}
    errCh                chan error
    started              bool // plain bool, no mutex
    setupVerifiers       []func(context.Context) error
    cleanupVerifiers     []func(context.Context) error
    // ...
}

// Start acquires lease and starts refresh goroutine
// Returns error if already started (NOT idempotent)
func (l *Leaser) Start(ctx context.Context) error

// Wait blocks until shutdown complete
func (l *Leaser) Wait() error

// Stop initiates shutdown then waits (idempotent)
func (l *Leaser) Stop(ctx context.Context) error

// SetupVerifiers returns functions that verify resources exist
func (l *Leaser) SetupVerifiers() []func(context.Context) error

// CleanupVerifiers returns functions that verify resources cleaned up
func (l *Leaser) CleanupVerifiers() []func(context.Context) error
```

**Test Helpers:**
- `CleanupTestLeaser(t, l)` - performs shutdown and verification
- `VerifyTestLeaserCleanup(t, l, ctx)` - runs all cleanup verifiers

**Verifiers Added During Startup:**
- Setup: etag file exists and has content
- Cleanup: refreshTicker is nil

**Status:** All 18 tests passing

### pkg/db (Database Manager)

**Current:**
```go
type Manager struct {
    errCh chan error
    // ...
}

// Start starts the database manager
func (m *Manager) Start(ctx context.Context) error

// Stop stops the database manager
func (m *Manager) Stop(ctx context.Context) error

// Wait blocks until Stop completes or panic
func (m *Manager) Wait() error
```

**Target:**
```go
type Manager struct {
    stopCh               chan struct{}
    stoppedCh            chan struct{}
    errCh                chan error
    started              bool
    setupVerifiers       []func(context.Context) error
    cleanupVerifiers     []func(context.Context) error
    // ...
}

// Start starts the database manager (MOSTLY UNCHANGED)
func (m *Manager) Start(ctx context.Context) error

// Wait blocks until shutdown complete (UNCHANGED)
func (m *Manager) Wait() error

// Stop initiates shutdown then waits (NEW if not present)
func (m *Manager) Stop(ctx context.Context) error

// SetupVerifiers returns setup verification functions (NEW)
func (m *Manager) SetupVerifiers() []func(context.Context) error

// CleanupVerifiers returns cleanup verification functions (NEW)
func (m *Manager) CleanupVerifiers() []func(context.Context) error
```

### pkg/juicefs (JuiceFS Manager)

**Current:**
```go
type JuiceFS struct {
    stopCh    chan struct{}
    stoppedCh chan struct{}
    errCh     chan error
    // ...
}

// Start starts JuiceFS mount
func (j *JuiceFS) Start(ctx context.Context) error

// Stop unmounts JuiceFS
func (j *JuiceFS) Stop(ctx context.Context) error

// Wait blocks until Stop completes
func (j *JuiceFS) Wait() error

// IsMounted checks if mounted
func (j *JuiceFS) IsMounted() bool
```

**Target:**
```go
type JuiceFS struct {
    stopCh               chan struct{}
    stoppedCh            chan struct{}
    errCh                chan error
    started              bool
    setupVerifiers       []func(context.Context) error
    cleanupVerifiers     []func(context.Context) error
    // ...
}

// Start starts JuiceFS mount (MOSTLY UNCHANGED)
func (j *JuiceFS) Start(ctx context.Context) error

// Wait blocks until shutdown complete (UNCHANGED)
func (j *JuiceFS) Wait() error

// Stop initiates shutdown then waits (UNCHANGED or minor updates)
func (j *JuiceFS) Stop(ctx context.Context) error

// SetupVerifiers returns setup verification functions (NEW)
func (j *JuiceFS) SetupVerifiers() []func(context.Context) error

// CleanupVerifiers returns cleanup verification functions (NEW)
func (j *JuiceFS) CleanupVerifiers() []func(context.Context) error

// IsMounted checks if mounted (UNCHANGED)
func (j *JuiceFS) IsMounted() bool
```

### pkg/overlay (Overlay Manager)

**Current:**
```go
type Manager struct {
    mountReady chan struct{}
    // NO stopCh, stoppedCh, errCh
    // ...
}

// Start mounts overlay and initializes checkpoints
func (m *Manager) Start(ctx context.Context, checkpointDBPath string) error

// Unmount unmounts overlay and checkpoints
func (m *Manager) Unmount(ctx context.Context) error

// NO Wait() method

// IsMounted checks if loopback mounted
func (m *Manager) IsMounted() bool

// IsOverlayFSMounted checks if overlay mounted
func (m *Manager) IsOverlayFSMounted() bool
```

**Target:**
```go
type Manager struct {
    mountReady           chan struct{}
    stopCh               chan struct{}     // NEW
    stoppedCh            chan struct{}     // NEW
    errCh                chan error        // NEW
    started              bool              // NEW
    setupVerifiers       []func(context.Context) error   // NEW
    cleanupVerifiers     []func(context.Context) error   // NEW
    // ...
}

// Start mounts overlay and initializes checkpoints (MOSTLY UNCHANGED)
func (m *Manager) Start(ctx context.Context, checkpointDBPath string) error

// Wait blocks until shutdown complete (NEW)
func (m *Manager) Wait() error

// Stop initiates shutdown then waits (NEW - wraps Unmount + Wait)
func (m *Manager) Stop(ctx context.Context) error

// SetupVerifiers returns setup verification functions (NEW)
func (m *Manager) SetupVerifiers() []func(context.Context) error

// CleanupVerifiers returns cleanup verification functions (NEW)
func (m *Manager) CleanupVerifiers() []func(context.Context) error

// Unmount unmounts overlay and checkpoints (UNCHANGED, kept for backward compat)
func (m *Manager) Unmount(ctx context.Context) error

// IsMounted checks if loopback mounted (UNCHANGED)
func (m *Manager) IsMounted() bool

// IsOverlayFSMounted checks if overlay mounted (UNCHANGED)
func (m *Manager) IsOverlayFSMounted() bool
```

### pkg/services (Services Manager)

**Current:**
```go
type Manager struct {
    commands      chan command
    stateRequests chan stateRequest
    ctx           context.Context
    cancel        context.CancelFunc
    // NO stopCh, stoppedCh, errCh
}

// Start initializes the database
func (m *Manager) Start() error

// Shutdown stops all services
func (m *Manager) Shutdown() error

// Close shuts down and closes DB
func (m *Manager) Close() error

// NO Wait() method
```

**Target:**
```go
type Manager struct {
    commands             chan command
    stateRequests        chan stateRequest
    ctx                  context.Context
    cancel               context.CancelFunc
    stopCh               chan struct{}  // NEW
    stoppedCh            chan struct{}  // NEW
    errCh                chan error     // NEW
    started              bool           // NEW
    setupVerifiers       []func(context.Context) error   // NEW
    cleanupVerifiers     []func(context.Context) error   // NEW
}

// Start initializes the database (MOSTLY UNCHANGED)
func (m *Manager) Start() error

// Wait blocks until shutdown complete (NEW)
func (m *Manager) Wait() error

// Stop stops all services then waits (RENAMED from Shutdown)
func (m *Manager) Stop(ctx context.Context) error

// SetupVerifiers returns setup verification functions (NEW)
func (m *Manager) SetupVerifiers() []func(context.Context) error

// CleanupVerifiers returns cleanup verification functions (NEW)
func (m *Manager) CleanupVerifiers() []func(context.Context) error

// Close shuts down and closes DB (UNCHANGED, kept for backward compat)
func (m *Manager) Close() error
```

## Verifier Functions Pattern

**Simplified Approach:**
Instead of complex ExternalResource structs, use simple verifier functions:

```go
// Added during startup for each external resource
setupVerifiers   []func(context.Context) error // check resources exist
cleanupVerifiers []func(context.Context) error // check resources cleaned up
```

**Example (pkg/leaser - implemented):**
```go
// When acquiring lease in Start():
l.setupVerifiers = append(l.setupVerifiers, func(ctx context.Context) error {
    // Check etag file exists and has content
    if _, err := os.Stat(l.etagFilePath); os.IsNotExist(err) {
        return fmt.Errorf("etag file does not exist: %s", l.etagFilePath)
    }
    data, err := os.ReadFile(l.etagFilePath)
    if err != nil {
        return fmt.Errorf("failed to read etag file: %w", err)
    }
    if len(bytes.TrimSpace(data)) == 0 {
        return fmt.Errorf("etag file is empty")
    }
    return nil
})

l.cleanupVerifiers = append(l.cleanupVerifiers, func(ctx context.Context) error {
    // Check ticker is nil (goroutine stopped)
    if l.refreshTicker != nil {
        return fmt.Errorf("refresh ticker still exists")
    }
    return nil
})
```

**Examples for Other Components:**

**pkg/db:**
- Setup: check litestream process running, check DB file exists
- Cleanup: check litestream process stopped, check leaser ticker nil

**pkg/juicefs:**
- Setup: check mount exists in /proc/mounts, check process running
- Cleanup: check mount gone from /proc/mounts, check no process

**pkg/overlay:**
- Setup: check loop device attached, check mounts in /proc/mounts
- Cleanup: check loop device detached, check mounts gone

**pkg/services:**
- Setup: check DB file exists, check log directory exists
- Cleanup: check no service processes running

## Test Helper Patterns

Each package exports:

```go
// CleanupTest<Component> performs shutdown and verification
func CleanupTest<Component>(t *testing.T, m *Manager) {
    t.Helper()
    
    ctx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
    defer cancel()
    
    if err := m.Stop(ctx); err != nil {
        t.Logf("Stop error (may be expected): %v", err)
    }
    
    VerifyTest<Component>Cleanup(t, m)
}

// VerifyTest<Component>Cleanup verifies all resources cleaned up
func VerifyTest<Component>Cleanup(t *testing.T, m *Manager) {
    t.Helper()
    
    if err := m.VerifyCleanup(); err != nil {
        resources := m.GetResources()
        t.Errorf("CLEANUP VERIFICATION FAILED for <component>: %v", err)
        
        for _, r := range resources {
            t.Errorf("  - Leaked %s: %s (%s)", r.Type, r.Identifier, r.Description)
        }
        
        // Print specific diagnostics based on resource types
        printDiagnostics(t, resources)
    }
}
```

## Shutdown Sequence Detail

**Phase 1: Prepare Container**
```
PrepareContainerForShutdown(ctx)
  ├─> ServicesManager.StopForUnmount()
  │   └─> Stop all service processes
  └─> StopProcess()
      └─> Kill container process
```

**Phase 2: Unmount Overlay**
```
OverlayManager.Stop(ctx)
  Internal order (REVERSE of startup):
  ├─> Unmount overlayfs (outermost)
  ├─> Unmount checkpoint mounts (deepest first)
  ├─> Sync and unmount ext4
  ├─> Detach loop devices
  └─> Wait for completion
```

**Phase 3: Stop JuiceFS**
```
JuiceFS.Stop(ctx)
  Internal order (REVERSE of startup):
  ├─> Find and unmount dependent mounts
  ├─> Sync JuiceFS mount
  ├─> juicefs umount --flush (up to 5min)
  └─> Wait for completion
```

**Phase 4: Stop Database Manager**
```
DBManager.Stop(ctx)
  Internal order (REVERSE of startup):
  ├─> Litestream.Stop()
  │   └─> SIGTERM, wait (up to 1min)
  ├─> Leaser.Stop()
  │   └─> Stop refresh, release lease
  └─> Wait for completion
```

**Phase 5-6: Network + Utilities**
```
APIServer.Stop(ctx)
SocketServer.Stop()
AdminChannel.Stop()
Reaper.Stop()
```

## Critical Requirements

1. **New() No Setup**: New() functions only initialize struct, NO setup work
2. **Strict Startup Order**: Each component must follow strict internal ordering
   - pkg/db: lease FIRST, then litestream
   - pkg/overlay: loop device, THEN ext4, THEN overlayfs
   - pkg/services: log dir, THEN database, THEN services
3. **Start() Idempotency**: Start() can be called multiple times safely
4. **Stop() Idempotency**: Stop() can be called multiple times safely
5. **Restartable**: Components can be started and stopped multiple times
6. **Wait Safety**: Wait() can be called multiple times, from multiple goroutines
7. **No Timeouts in Methods**: Cleanup methods do NOT timeout (system level handles this)
8. **Force Cleanup**: Even on error, resources MUST be cleaned up
9. **Reverse Order Cleanup**: Stop() must reverse the order of Start()
10. **System Sequence Unchanged**: Overall system startup/shutdown sequence stays same
11. **Preserved Critical Timeouts**: 
    - JuiceFS umount: up to 5 minutes (data integrity)
    - Litestream shutdown: up to 1 minute (data integrity)

## Test Requirements

Every component test must:
1. Use package test helpers for cleanup
2. Verify no resource leaks after cleanup
3. Fail with specific error messages showing leaked resources
4. Suggest debugging commands for leaked resources
5. Test cleanup under error conditions
6. Test multiple Start() calls (idempotency)
7. Test multiple Stop() calls (idempotency)
8. Test multiple Wait() calls (safety)
9. Test full restart cycle: Start() → Stop() → Start() → Stop()
