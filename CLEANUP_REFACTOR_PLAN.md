# System Component Cleanup Refactoring Plan

## Overview

This plan standardizes how all pkg/ modules that manage external resources handle lifecycle and cleanup. The goal is to make shutdown behavior predictable, testable, and properly isolated to each package.

## Quick Start - Implementation Pattern (from pkg/leaser)

**Add to struct:**
```go
type Manager struct {
    stopCh               chan struct{}
    stoppedCh            chan struct{}
    errCh                chan error
    started              bool // plain bool, no mutex
    setupVerifiers       []func(context.Context) error
    cleanupVerifiers     []func(context.Context) error
    // ... other fields ...
}
```

**In Start():**
```go
func (m *Manager) Start(ctx context.Context) error {
    if m.started {
        return fmt.Errorf("manager already started")
    }
    m.started = true
    m.setupVerifiers = nil
    m.cleanupVerifiers = nil
    
    // Setup resources, add verifiers as you go:
    m.setupVerifiers = append(m.setupVerifiers, func(ctx context.Context) error {
        // Check filesystem, /proc, etc.
        return nil
    })
    m.cleanupVerifiers = append(m.cleanupVerifiers, func(ctx context.Context) error {
        // Check resource is gone
        return nil
    })
    
    return nil
}
```

**Add getters:**
```go
func (m *Manager) SetupVerifiers() []func(context.Context) error {
    return m.setupVerifiers
}

func (m *Manager) CleanupVerifiers() []func(context.Context) error {
    return m.cleanupVerifiers
}
```

**In tests:**
```go
// After Start()
for i, verify := range mgr.SetupVerifiers() {
    if err := verify(ctx); err != nil {
        t.Errorf("Setup verifier %d failed: %v", i, err)
    }
}

// After Stop()
for i, verify := range mgr.CleanupVerifiers() {
    if err := verify(ctx); err != nil {
        t.Errorf("Cleanup verifier %d failed: %v", i, err)
    }
}
```

**Do NOT:**
- Add VerifySetup() or VerifyCleanup() methods
- Create ExternalResource struct or any interface
- Use mutex/atomic for started flag
- Track internal Go values (unless they represent external resources)

**Reference:** See pkg/leaser for complete working example

## Problem Statement

Currently, cleanup during shutdown is inconsistent and "dirty":
- Different packages have different shutdown APIs (Stop, Shutdown, Close, Unmount)
- Some have Wait(), some don't
- Verification of proper cleanup is scattered across test helpers
- Resource tracking is ad-hoc
- Tests have complex cleanup logic that should be in the packages themselves

## Core Principles

1. **Uniform Interface**: All resource-managing packages expose identical lifecycle methods
2. **No Setup in New()**: New() functions only initialize struct, all setup happens in Start()
3. **Strict Startup Order**: Each component must follow strict internal ordering (e.g., lease before litestream)
4. **Reverse Cleanup Order**: Stop() must clean up in reverse order of Start()
5. **Start() Returns Error if Running**: Start() errors if already started (NOT idempotent)
6. **Stop() IS Idempotent**: Stop() can be called multiple times safely
7. **Restartable**: Components can go through Start() → Stop() → Start() cycles
8. **Complete Cleanup**: Even on error, resources MUST be forcefully cleaned up
9. **No Timeouts in Cleanup**: Packages do cleanup without timeouts (system level handles timeouts)
10. **Isolated to Packages**: Tests and system/ should not manage cleanup details
11. **Simple Verifier Functions**: Two slices of verification functions, no complex structs
12. **Verifiers Check Only System State**: Check filesystem, /proc, mounts - NOT internal Go values
13. **Coordinators Have No Verifiers**: Components that only coordinate sub-components have no verifiers

## Critical Ordering Requirements

Each component MUST follow strict internal ordering during startup and cleanup:

### pkg/db (Database Manager)
**Startup Order:**
1. Acquire lease (MUST complete first)
2. Start litestream (depends on lease)

**Cleanup Order (reverse):**
1. Stop litestream
2. Release lease

### pkg/juicefs (JuiceFS Manager)
**Startup Order:**
1. Create directories
2. Format if needed
3. Start mount process
4. Wait for mount ready
5. Post-mount setup

**Cleanup Order (reverse):**
1. Unmount dependents
2. Sync
3. Unmount main mount

### pkg/overlay (Overlay Manager) - CRITICAL
**Startup Order:**
1. Create image file
2. Attach loop device (MUST complete before next step)
3. Format ext4 if needed
4. Mount ext4 on loop device (MUST complete before next step)
5. Mount overlayfs (depends on ext4 being mounted)
6. Setup checkpoint infrastructure
7. Mount checkpoints (async)

**Cleanup Order (reverse):**
1. Unmount overlayfs first
2. Unmount checkpoints
3. Sync and unmount ext4
4. Detach loop device last

### pkg/services (Services Manager)
**Startup Order:**
1. Create log directory (MUST exist before services)
2. Open database (MUST exist before services)
3. Services can now be started

**Cleanup Order (reverse):**
1. Stop all services
2. Close database

### pkg/leaser (S3 Lease Manager)
**Startup Order:**
1. Try to acquire lease
2. Write etag file
3. Start refresh goroutine

**Cleanup Order (reverse):**
1. Stop refresh goroutine
2. Close channels

## System Components That Manage External Resources

### 1. pkg/db (Database Manager) ✅ PHASE 1 COMPLETE
**Role:** Coordinator - manages startup/shutdown order of sub-components

**Sub-Components:**
- Leaser (S3 lease object + local etag file) - has its own verifiers
- Litestream subprocess (manages replication) - will have its own verifiers

**Strict Startup Order:**
1. FIRST: Acquire lease via Leaser.Start() - MUST complete before litestream
2. THEN: Start litestream replication
3. THEN: Mark as started

**Implemented:**
- New(config) - creates manager, initializes channels
- Start(ctx) - acquires lease, starts litestream
- Stop(ctx) - stops litestream then leaser (reverse order)
- Wait() - blocks until stopped or panic
- GetLeaser() - returns leaser for test verification
- GetLitestream() - returns litestream for test verification
- SetupVerifiers() and CleanupVerifiers() - return empty slices (coordinator has no direct resources)
- StopLitestream(ctx), StartLitestream(ctx) - control litestream independently

**Key Design:** 
- db.Manager is a coordinator with NO direct external resources
- Tests verify sub-components separately using GetLeaser() and GetLitestream()
- Follows composition over aggregation - each component responsible for its own verification

### 2. pkg/juicefs (JuiceFS Manager)
**External Resources:**
- JuiceFS mount process (daemon)
- Mount point in /proc/mounts
- Cache directory with files
- Metadata database file handles

**Strict Startup Order:**
1. FIRST: Create directories
2. THEN: Format if needed (check then format)
3. THEN: Start mount process
4. THEN: Wait for mount ready
5. THEN: Perform post-mount setup (dirs, quota)
6. THEN: Mark as started

**Current State:**
- New(config) - creates manager, NO setup
- Start(ctx) - formats if needed, starts mount, waits for ready
- Stop(ctx) - unmounts dependents, syncs, umount --flush, waits up to 5min
- Wait() - blocks until stoppedCh or panic
- WhenReady(ctx) - blocks until mount ready
- IsMounted() - checks if mounted

**What Needs to Change:**
- Add started bool flag if missing
- Add setupVerifiers, cleanupVerifiers slices
- Make Start() error if already started
- Make Stop() idempotent (verify)
- Make Stop() reset started flag for restartability
- Ensure Wait() can be called multiple times (already can)
- Add SetupVerifiers() and CleanupVerifiers() getters
- Populate verifiers during Start(): mount in /proc/mounts, process running
- Cleanup verifiers: mount gone, process stopped
- Stop() cleanup order: dependents, sync, main mount, mark stopped

### 3. pkg/overlay (Overlay Manager)
**External Resources:**
- Loop devices (/dev/loopX)
- Loopback mount (ext4 on loop device)
- OverlayFS mount (overlay on top of ext4)
- Checkpoint mounts (additional loop devices + mounts)

**Strict Startup Order (CRITICAL):**
1. FIRST: Create image file if needed
2. THEN: Attach loop device to image
3. THEN: Format ext4 on loop device if needed
4. THEN: Mount ext4 on loop device (MUST complete before overlay)
5. THEN: Mount overlayfs using ext4 as upper
6. THEN: Setup checkpoint infrastructure
7. THEN: Mount existing checkpoints (async, non-blocking)
8. THEN: Mark as started

**Current State:**
- New(config) - creates manager, initializes channels
- Start(ctx, dbPath) - mounts overlay, initializes checkpoints
- Mount(ctx) - creates image, attaches loop, mounts ext4, mounts overlay
- Unmount(ctx) - unmounts overlay, ext4, detaches loop, unmounts checkpoints
- IsOverlayFSMounted(), IsMounted() - check mount state
- NO Wait() method

**What Needs to Change:**
- Add stopCh/stoppedCh/errCh if not present
- Add started bool flag
- Add setupVerifiers, cleanupVerifiers slices
- Add Wait() - blocks until shutdown complete
- Make Start() error if already started
- Make Unmount() idempotent - needs verification
- Make Unmount() reset started flag for restartability
- Ensure Wait() can be called multiple times
- Add SetupVerifiers() and CleanupVerifiers() getters
- Populate verifiers during Start(): loop devices attached, mounts in /proc/mounts
- Cleanup verifiers: loop devices detached, mounts gone from /proc/mounts
- Ensure Start() follows strict order: loop device THEN ext4 THEN overlay
- Unmount() cleanup order: overlay, checkpoints, ext4, loop device (reverse)

### 4. pkg/leaser (S3 Lease Manager) ✅ COMPLETE
**External Resources:**
- S3 lease object (sprite.lock)
- Local etag file (.sprite-lease-etag)
- Background refresh ticker + goroutine

**Strict Startup Order:**
1. FIRST: Try to acquire lease (with existing etag if available)
2. THEN: If successful, write etag to file
3. THEN: Start refresh goroutine
4. THEN: Add verifiers for resources

**Implemented:**
- New(config) - creates leaser, NO setup
- Start(ctx) - acquires lease, starts refresh, adds verifiers
- Wait() - blocks on stoppedCh/errCh
- Stop(ctx) - stops ticker, closes channels, resets started flag
- SetupVerifiers() - returns functions to verify etag file exists/has content
- CleanupVerifiers() - returns functions to verify ticker is nil

**Verifiers Added:**
- Setup: Check etag file exists and has content
- Cleanup: Check refreshTicker is nil (goroutine stopped)

### 5. pkg/services (Services Manager)
**External Resources:**
- Service processes (PIDs)
- Service database file
- Log files

**Strict Startup Order:**
1. FIRST: Create log directory (MUST exist before starting services)
2. THEN: Open/create services database (MUST exist before starting services)
3. THEN: Mark as started (services can now be started)
4. Services are started separately via StartService() or StartAll()

**Current State:**
- NewManager(dataDir) - creates manager, starts run() goroutine
- Start() - initializes database
- Shutdown() - stops all services in reverse dependency order
- Close() - calls Shutdown() then closes DB
- StopForUnmount() - Shutdown + close DB, keep context alive
- NO Wait() method - run() goroutine runs until context cancelled

**What Needs to Change:**
- Add stopCh/stoppedCh/errCh to Manager if missing
- Add started bool flag
- Add setupVerifiers, cleanupVerifiers slices
- Ensure NewManager() does NO setup, only struct init and start run()
- Ensure Start() creates log dir THEN opens DB (strict order)
- Make Start() error if already started
- Add Wait() - blocks until all services stopped
- Rename Shutdown() to Stop() for consistency
- Make Stop() idempotent
- Make Stop() reset started flag for restartability
- Ensure Wait() can be called multiple times
- Add SetupVerifiers() and CleanupVerifiers() getters
- Populate verifiers during Start(): DB file exists, log dir exists
- Cleanup verifiers: no service processes running
- Keep StopForUnmount() behavior for restore scenarios
- Make run() close stoppedCh when context cancelled
- Stop() cleanup order: stop services (reverse dependency), close DB

## Standard Interface Pattern

Every resource-managing package will implement this pattern:

```go
type Manager struct {
    // ... existing fields ...
    
    // Lifecycle channels
    stopCh     chan struct{} // closed to request shutdown
    stoppedCh  chan struct{} // closed when shutdown complete
    errCh      chan error    // buffered, reports panics
    
    // State (plain bool, no mutex needed for simple flag)
    started    bool
    
    // Verifiers for external resources (check actual system state)
    setupVerifiers   []func(context.Context) error // verify resources exist
    cleanupVerifiers []func(context.Context) error // verify resources cleaned up
}

// New creates a new manager instance
// Does NOT perform any setup - only initializes the struct
// All actual setup happens in Start()
func New(config Config) (*Manager, error) {
    m := &Manager{
        config:    config,
        stopCh:    make(chan struct{}),
        stoppedCh: make(chan struct{}),
        errCh:     make(chan error, 1),
    }
    // NO setup work here, just struct initialization
    return m, nil
}

// Start begins operations and sets up resources in STRICT ORDER
// Returns when setup is complete and resources are ready
// Returns ERROR if already started (not idempotent)
func (m *Manager) Start(ctx context.Context) error {
    if m.started {
        return fmt.Errorf("manager already started")
    }
    m.started = true
    
    // Clear verifiers from any previous run
    m.setupVerifiers = nil
    m.cleanupVerifiers = nil
    
    // Setup resources in STRICT ORDER
    // Each step MUST complete before next step begins
    // As resources are acquired, add verifiers
    // Example for db manager:
    //   1. Acquire lease (MUST complete first)
    //      - Add setup verifier: check lease file exists
    //      - Add cleanup verifier: check ticker nil
    //   2. Start litestream (depends on lease)
    //      - Add setup verifier: check process running
    //      - Add cleanup verifier: check process stopped
    
    return nil
}

// Wait blocks until Stop() completes or a panic occurs
// Can be called multiple times safely
func (m *Manager) Wait() error {
    select {
    case <-m.stoppedCh:
        return nil
    case err := <-m.errCh:
        return err
    }
}

// Stop initiates shutdown then waits for completion
// Can be called multiple times safely (idempotent)
// May return error but MUST forcefully clean up even on error
func (m *Manager) Stop(ctx context.Context) error {
    // Signal shutdown
    select {
    case <-m.stopCh:
        // Already stopping
    default:
        close(m.stopCh)
    }
    
    // Do cleanup work in REVERSE ORDER of startup
    err := m.cleanup(ctx)
    
    // Close stoppedCh
    select {
    case <-m.stoppedCh:
        // Already closed
    default:
        close(m.stoppedCh)
    }
    
    // Mark as not started so it can be restarted
    m.started = false
    
    return err
}

// SetupVerifiers returns functions that verify resources are set up correctly
// Each function checks actual system state (files, processes, mounts, etc.)
func (m *Manager) SetupVerifiers() []func(context.Context) error {
    return m.setupVerifiers
}

// CleanupVerifiers returns functions that verify resources are cleaned up
// Each function checks actual system state (files, processes, mounts, etc.)
func (m *Manager) CleanupVerifiers() []func(context.Context) error {
    return m.cleanupVerifiers
}
```

## Verifier Functions Pattern

Instead of a complex ExternalResource struct, we use simple verifier functions:

```go
// Setup verifiers check that resources exist (added during startup)
setupVerifiers []func(context.Context) error

// Cleanup verifiers check that resources are cleaned up (added during startup)
cleanupVerifiers []func(context.Context) error
```

**Example (pkg/leaser):**
```go
// When acquiring lease, add verifiers:
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

**Key Points:**
- Verifiers ONLY check actual system state (filesystem, /proc, mounts, etc.)
- Do NOT add verifiers for internal Go values unless they represent external resources
- If resources don't need cleanup verification, only add setup verifier
- Simple functions, easy to test and debug

## Test Helper Pattern

Each package exports test helpers:

```go
// CleanupTest<Component> performs cleanup and verification
func CleanupTest<Component>(t *testing.T, m *Manager) {
    t.Helper()
    
    ctx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
    defer cancel()
    
    if err := m.Stop(ctx); err != nil {
        t.Logf("Stop error: %v", err)
    }
    
    VerifyTest<Component>Cleanup(t, m, ctx)
}

// VerifyTest<Component>Cleanup verifies all resources are cleaned up
func VerifyTest<Component>Cleanup(t *testing.T, m *Manager, ctx context.Context) {
    t.Helper()
    
    // Check channels are closed
    select {
    case <-m.stopCh:
    default:
        t.Errorf("CLEANUP FAILED: stopCh not closed")
    }
    select {
    case <-m.stoppedCh:
    default:
        t.Errorf("CLEANUP FAILED: stoppedCh not closed")
    }
    
    // Run all cleanup verifiers
    verifiers := m.CleanupVerifiers()
    for i, verify := range verifiers {
        if err := verify(ctx); err != nil {
            t.Errorf("CLEANUP VERIFICATION FAILED (verifier %d): %v", i, err)
        }
    }
}
```

## Server/System Interface (Optional)

server/system MAY define a simple interface:

```go
// SystemComponent represents a lifecycle-managed system component
type SystemComponent interface {
    Wait() error
    Shutdown(ctx context.Context) error
}

// ExternalResourceManager extends SystemComponent with resource tracking
type ExternalResourceManager interface {
    SystemComponent
    GetResources() []ExternalResource
    VerifySetup() error
    VerifyCleanup() error
}
```

This is OPTIONAL - the important thing is that all components implement the same pattern, not that they implement a shared interface.

## Startup/Shutdown Sequences (UNCHANGED)

### Startup Order (from system_boot.go):
1. Utilities (Reaper, AdminChannel, ResourceMonitor)
2. Network services (APIServer, SocketServer)
3. Storage:
   - DBManager.Start()
   - JuiceFS.Start()
   - OverlayManager.Start()
4. Container process
5. ServicesManager.Start()
6. ActivityMonitor

### Shutdown Order (from system_shutdown.go):
1. ActivityMonitor.Stop()
2. PrepareContainerForShutdown:
   - ServicesManager.StopForUnmount()
   - StopProcess()
3. OverlayManager.Unmount()
4. JuiceFS.Stop()
5. DBManager.Stop()
6. Network services (APIServer, SocketServer)
7. Utilities (AdminChannel, Reaper)

**This sequence does not change.** We're just standardizing the API for each step.

## Migration Strategy

### Phase 1: Add infrastructure (no behavior changes)
1. Add stopCh/stoppedCh/errCh to each component if missing
2. Add started bool flag
3. Add setupVerifiers and cleanupVerifiers slices
4. Add Wait() method to components missing it
5. Make Start() error if already started
6. Make Stop() reset started flag
7. Add SetupVerifiers() and CleanupVerifiers() getters (return empty slices)

### Phase 2: Implement verification
1. Add helper function to populate verifiers during startup
2. Call helper after each resource is acquired in Start()
3. Setup verifiers: check system state (files exist, processes running, mounts present)
4. Cleanup verifiers: check system state (processes stopped, mounts gone, loop devices detached)
5. Add test helpers to each package
6. Tests call verifiers directly - no wrapper methods needed

### Phase 3: Integration
1. Update system/ to use new APIs (Start/Wait/Stop)
2. Update any existing code that uses old API
3. Verify backward compatibility if needed

### Phase 4: Validation
1. Run full test suite after each component
2. Verify no resource leaks (run cleanup verifiers)
3. Verify proper error messages on leaked resources
4. Test shutdown under various failure scenarios
5. Test multiple Start() calls (should error)
6. Test multiple Stop() calls (should work)
7. Test restart cycles (Start → Stop → Start)

## Success Criteria

1. ✅ All resource-managing packages have: Start(), Wait(), Stop()
2. ✅ All resource-managing packages have: SetupVerifiers(), CleanupVerifiers()
3. ✅ All New() functions do NO setup work - only struct initialization
4. ✅ All Start() methods follow strict internal ordering
5. ✅ Start() ERRORS if already started (NOT idempotent) - catches programming bugs
6. ✅ All Stop() methods ARE idempotent - can call multiple times safely
7. ✅ Wait() can be called multiple times from multiple goroutines
8. ✅ Components can be started and stopped multiple times (full lifecycle)
9. ✅ Each package exports CleanupTest and VerifyTestCleanup helpers
10. ✅ Tests call verifiers directly (no VerifySetup/VerifyCleanup methods)
11. ✅ Failed cleanup produces detailed diagnostics from verifiers
12. ✅ No resource leaks in test suite
13. ✅ System startup sequence unchanged
14. ✅ System shutdown sequence unchanged
15. ✅ Critical startup orders preserved (lease before litestream, loop before overlay, etc.)
16. ✅ Verifiers check ONLY system state (filesystem, /proc, loop devices), NOT internal Go values
17. ✅ Verifiers are simple: `func(context.Context) error`
18. ✅ Verifiers populated during startup, cleared on each Start()
19. ✅ No complex structs or interfaces - just function slices
20. ✅ If resource doesn't need cleanup verification, only add setup verifier

## Components Not Requiring Changes

These components don't manage external resources requiring cleanup:
- pkg/port-watcher - uses global singleton monitor
- pkg/container - simple PTY creation, cleanup via Close()
- pkg/sync - network client/server, no external resources
- pkg/tap - logging utilities
- pkg/terminal - tmux utilities
- pkg/tmux - tmux interaction
- pkg/wsexec - WebSocket execution utilities

## Testing Requirements

### Unit Tests
Each package must have tests that:
1. Verify Start() sets up resources correctly
2. Verify Stop() cleans up resources completely
3. Verify Wait() blocks until shutdown complete
4. Verify Stop() is idempotent
5. Verify Wait() can be called multiple times
6. Verify cleanup happens even on errors
7. Verify setup verifiers pass after Start()
8. Verify cleanup verifiers pass after Stop()
9. Verify Start() errors if called twice without Stop()
10. Verify restart cycle works (Start → Stop → Start → Stop)

### Integration Tests
System tests must:
1. Verify proper startup sequence
2. Verify proper shutdown sequence
3. Verify no resource leaks after shutdown (call cleanup verifiers)
4. Use package test helpers for cleanup
5. Fail with detailed diagnostics on resource leaks (from verifier errors)

## Critical Timeouts to Preserve

From memory 2978565:
- JuiceFS umount --flush: up to 5 minutes
- Litestream shutdown: up to 1 minute

These are data integrity timeouts and must NOT be reduced.

## Implementation Notes

### For pkg/db:
- Leaser is a sub-component, not a direct resource
- Need to expose both Litestream and Leaser resources
- StopLitestream/StartLitestream remain for restore scenarios

### For pkg/juicefs:
- Must handle dependent mounts (overlays using JuiceFS)
- findAndUnmountDependentMounts stays as-is
- 5-minute timeout is in umount itself, not in Stop()

### For pkg/overlay:
- Most complex: loop devices + multiple mounts + checkpoints
- CRITICAL: loop device MUST be mounted (as ext4) before overlayfs mount
- Must start in strict order: loop attach → ext4 mount → overlayfs mount
- Must unmount in correct order (reverse): overlayfs → ext4 → loop detach
- Must unmount checkpoints before main overlay
- Must detach loop devices after all mounts gone
- Must be restartable: Start() after Stop() should work
- GetResources() must list ALL loop devices and mounts

### For pkg/leaser: ✅ COMPLETE
- Split Wait() into Start() + Wait()
- Start() does lease acquisition + starts refresh + adds verifiers
- Wait() just blocks on stoppedCh
- Fully restartable: Start() after Stop() works
- Verifiers added: etag file exists/has content (setup), ticker nil (cleanup)
- Tests updated to use new API
- All 18 tests passing

### For pkg/services:
- Already has good shutdown logic
- CRITICAL: log directory MUST exist before starting services
- CRITICAL: database MUST be open before starting services
- Start() must create log dir then open DB (strict order)
- Just needs Wait() method
- Rename Shutdown() to Stop() for consistency
- Must be restartable: Start() after Stop() should work
- StopForUnmount remains for restore scenarios
- VerifyCleanup checks no processes still running, DB closed

## Resource Tracking - Simplified Approach

**DO NOT:**
- Create complex structs or interfaces
- Add VerifySetup() / VerifyCleanup() methods
- Track internal Go values unless they represent external resources
- Use ExternalResource struct

**DO:**
- Use two simple slices:
  ```go
  setupVerifiers   []func(context.Context) error
  cleanupVerifiers []func(context.Context) error
  ```
- Add verifiers as resources are acquired in Start()
- Verifiers check ONLY system state: filesystem, /proc/mounts, process tables, loop devices
- Tests iterate verifiers and call them directly
- Provide clear error messages from each verifier

**Example Verifier (pkg/leaser):**
```go
l.setupVerifiers = append(l.setupVerifiers, func(ctx context.Context) error {
    // Check etag file exists
    if _, err := os.Stat(l.etagFilePath); os.IsNotExist(err) {
        return fmt.Errorf("etag file does not exist: %s", l.etagFilePath)
    }
    // Check etag file has content
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
    if l.refreshTicker != nil {
        return fmt.Errorf("refresh ticker still exists - goroutine may not have stopped")
    }
    return nil
})
```

## Risk Mitigation

1. **No behavior changes in Phase 1** - just adds infrastructure
2. **Verification before enforcement** - Phase 2 adds checks, doesn't fail yet
3. **Gradual rollout** - one package at a time
4. **Comprehensive testing** - verify each change with full test suite
5. **Preserved setup** - zero changes to how things start up
6. **Preserved sequences** - shutdown order stays the same
7. **Backward compatibility** - old Stop/Unmount methods still work

## Dependencies Between Components

Critical ordering (must be preserved):
1. OverlayManager depends on JuiceFS (image file on JuiceFS)
2. JuiceFS depends on DBManager (metadata DB)
3. ServicesManager depends on container process
4. Container process depends on OverlayManager

Shutdown must go in reverse:
1. Stop ServicesManager
2. Stop container process
3. Unmount OverlayManager
4. Stop JuiceFS
5. Stop DBManager

Each component is ignorant of others - system/ orchestrates the sequence.

## Progress

### ✅ pkg/leaser - COMPLETE (Phases 1 & 2)
- [x] Phase 1: Infrastructure added
- [x] Phase 2: Verification implemented  
- [x] All 18 tests passing
- [x] Test helpers: CleanupTestLeaser(), VerifyTestLeaserCleanup()
- Phase 3: Will be done after other components standardized

**Final Design (Simplified):**
- No mutex/atomic for simple flags - plain `bool` is sufficient
- Start() errors if already started (catches programming bugs)
- Stop() is idempotent
- Simple verifier functions instead of complex ExternalResource struct:
  - `setupVerifiers []func(context.Context) error`
  - `cleanupVerifiers []func(context.Context) error`
- Verifiers ONLY check system state (files exist, ticker nil), not internal flags
- Verifiers added during startup with helper function
- Tests call verifiers directly - no VerifySetup/VerifyCleanup methods needed

### Next: pkg/db
1. Add infrastructure (Phase 1)
2. Implement verification (Phase 2)
3. Update tests
4. Then move to pkg/juicefs, pkg/overlay, pkg/services

Total estimate: ~2-3 days of work remaining, one component at a time.
