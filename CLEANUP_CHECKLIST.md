# Cleanup Refactoring Implementation Checklist

## Component Inventory

### ✅ Components Requiring Standardization
- [x] pkg/leaser - S3 lease manager (Phases 1 & 2 COMPLETE)
- [ ] pkg/db - Database + Litestream + Leaser wrapper
- [ ] pkg/juicefs - JuiceFS mount manager
- [ ] pkg/overlay - Overlay + loop device manager
- [ ] pkg/services - Service process manager

### ✅ Components NOT Requiring Changes
- pkg/port-watcher - uses global singleton, no cleanup needed
- pkg/container - simple PTY creation
- pkg/sync - network utilities
- pkg/tap - logging utilities
- pkg/terminal - tmux utilities
- pkg/tmux - tmux interaction
- pkg/wsexec - WebSocket execution

## Phase 1: Infrastructure (No Behavior Changes)

### pkg/leaser ✅ COMPLETE
- [x] Verify New() does NO setup work (confirmed correct)
- [x] Add stopCh, stoppedCh, errCh (already present, errCh added)
- [x] Split Wait() into Start() + Wait()
- [x] Make Start() ERROR if already started (not idempotent - returns error)
- [x] Make Stop() idempotent (confirmed correct)
- [x] Make Stop() reset started flag for restartability
- [x] Add resources []ExternalResource field to track acquired resources
- [x] Add GetResources() stub → return []ExternalResource{}
- [x] Add VerifySetup() stub → return nil
- [x] Add VerifyCleanup() stub → return nil
- [x] Add tests verifying: multiple Start(), multiple Stop(), restart cycle
- [x] Add tests verifying no behavior change

### pkg/db ✅ PHASE 1 COMPLETE
- [x] Verify New() does NO setup work (confirmed correct)
- [x] Verify Start() follows strict order: lease FIRST, then litestream (confirmed correct)
- [x] Add stopCh, stoppedCh to Manager
- [x] Make Start() ERROR if already started (not idempotent - returns error)
- [x] Make Stop() idempotent (confirmed correct)
- [x] Make Stop() reset started flag for restartability
- [x] Verify Wait() can be called multiple times (updated to use stoppedCh)
- [x] Add setupVerifiers and cleanupVerifiers slices
- [x] Add SetupVerifiers() and CleanupVerifiers() getter methods
- [x] Add tests verifying: multiple Start(), multiple Stop(), restart cycle
- [x] Add tests verifying no behavior change (all 11 tests passing)

### pkg/juicefs ✅ PHASE 1 COMPLETE
- [x] Verify New() does NO setup work (confirmed correct)
- [x] Verify Start() follows strict order: dirs, format, mount, wait, post-setup (confirmed correct)
- [x] Verify stopCh, stoppedCh, errCh present (already are)
- [x] Add started bool flag
- [x] Make Start() ERROR if already started (not idempotent - returns error)
- [x] Make Stop() idempotent (confirmed correct)
- [x] Make Stop() reset started flag for restartability
- [x] Recreate channels in Start() for restartability
- [x] Verify Wait() can be called multiple times (confirmed correct)
- [x] Add setupVerifiers and cleanupVerifiers slices
- [x] Add SetupVerifiers() and CleanupVerifiers() getter methods
- [x] Add lifecycle_test.go with Phase 1 tests (4 tests passing)

### pkg/overlay
- [ ] Verify New() does NO setup work (should be correct already)
- [ ] CRITICAL: Verify Start() follows strict order: loop, ext4, overlay
- [ ] Add stopCh, stoppedCh, errCh to Manager
- [ ] Add Wait() method that blocks on stoppedCh
- [ ] Make Start() idempotent - check mount state
- [ ] Make Unmount() signal stoppedCh when done
- [ ] Make Unmount() idempotent - check mount state
- [ ] Make Unmount() reset state for restartability
- [ ] CRITICAL: Verify Unmount() reverses order: overlay, checkpoints, ext4, loop
- [ ] Add GetResources() stub → return []ExternalResource{}
- [ ] Add VerifySetup() stub → return nil
- [ ] Add VerifyCleanup() stub → return nil
- [ ] Add tests verifying: multiple Start(), multiple Unmount(), restart cycle
- [ ] Add tests verifying no behavior change

### pkg/services
- [ ] Verify NewManager() does NO setup work (only struct init + start run())
- [ ] CRITICAL: Verify Start() follows strict order: log dir FIRST, then DB
- [ ] Add stopCh, stoppedCh, errCh to Manager
- [ ] Add Wait() method that blocks on stoppedCh
- [ ] Make run() close stoppedCh when context cancelled
- [ ] Make Start() idempotent - check DB state
- [ ] Make Stop() idempotent (rename from Shutdown)
- [ ] Make Stop() reset state for restartability
- [ ] Add GetResources() stub → return []ExternalResource{}
- [ ] Add VerifySetup() stub → return nil
- [ ] Add VerifyCleanup() stub → return nil
- [ ] Add tests verifying: multiple Start(), multiple Stop(), restart cycle
- [ ] Add tests verifying no behavior change

## Phase 2: Implement Verification

### pkg/leaser ✅ COMPLETE
- [x] Add setupVerifiers and cleanupVerifiers slices to struct
- [x] Populate verifiers during Start() with trackResources() helper
- [x] Implement SetupVerifiers() - returns []func(context.Context) error
- [x] Implement CleanupVerifiers() - returns []func(context.Context) error
- [x] Verifiers check ONLY system state (files, ticker), not internal flags
- [x] Add test_helpers.go with CleanupTestLeaser(), VerifyTestLeaserCleanup()
- [x] Write tests for verification functions (4 new tests, all pass)
- [x] Removed VerifySetup() and VerifyCleanup() methods (use verifiers in tests instead)

### pkg/db
- [x] Add setupVerifiers and cleanupVerifiers slices
- [x] db.Manager has NO verifiers - it's a coordinator with no direct external resources
- [x] Sub-component verifiers: accessed via GetLeaser() and GetLitestream()
- [x] Tests verify each sub-component separately (composition, not aggregation)
- [x] Implement SetupVerifiers() and CleanupVerifiers() getter methods (return empty slices)
- [x] Add test_helpers.go with CleanupTestDB(), VerifyTestDBCleanup()
- [ ] Future: Add verifiers to Litestream struct itself (separate task)

### pkg/juicefs
- [ ] Add setupVerifiers and cleanupVerifiers slices
- [ ] Populate verifiers during Start()
- [ ] Setup verifiers: mount in /proc/mounts, process running
- [ ] Cleanup verifiers: mount gone from /proc/mounts, no process
- [ ] Implement SetupVerifiers() and CleanupVerifiers()
- [ ] Enhance test_helpers.go (already exists) with new verification
- [ ] Write tests for verification functions

### pkg/overlay
- [ ] Add setupVerifiers and cleanupVerifiers slices
- [ ] Populate verifiers during Start()
- [ ] Setup verifiers: loop devices attached (losetup -a), mounts in /proc/mounts
- [ ] Cleanup verifiers: loop devices detached, mounts gone from /proc/mounts
- [ ] Implement SetupVerifiers() and CleanupVerifiers()
- [ ] Enhance test_helpers.go (already exists) with new verification
- [ ] Write tests for verification functions

### pkg/services
- [ ] Add setupVerifiers and cleanupVerifiers slices
- [ ] Populate verifiers during Start()
- [ ] Setup verifiers: DB file exists and accessible, log directory exists
- [ ] Cleanup verifiers: no service processes running (check /proc or ps)
- [ ] Implement SetupVerifiers() and CleanupVerifiers()
- [ ] Add test_helpers.go with CleanupTestServices(), VerifyTestServicesCleanup()
- [ ] Write tests for verification functions

## Phase 3: Standardize Lifecycle

### pkg/leaser
- [ ] Verify Stop() already wraps cleanup + Wait() pattern
- [ ] Update server/system to use Start() instead of Wait()
- [ ] Update tests to use Start() + separate Wait() where needed
- [ ] Verify backward compatibility

### pkg/db
- [ ] Verify Stop() already follows pattern
- [ ] No changes needed - already correct
- [ ] Verify backward compatibility

### pkg/juicefs
- [ ] Verify Stop() already follows pattern
- [ ] No changes needed - already correct
- [ ] Verify backward compatibility

### pkg/overlay
- [ ] Add Stop(ctx) wrapper: call Unmount(ctx) internally
- [ ] Keep Unmount() public for backward compatibility
- [ ] Update server/system to use Stop() instead of Unmount()
- [ ] Verify backward compatibility

### pkg/services
- [ ] Rename Shutdown() to Stop() for consistency
- [ ] Keep Close() for backward compatibility
- [ ] Update server/system to use Stop() instead of Shutdown()
- [ ] Verify backward compatibility

## Phase 4: Update Tests

### pkg/leaser tests
- [ ] Replace ad-hoc cleanup with CleanupTestLeaser()
- [ ] Add VerifyTestLeaserCleanup() after cleanup
- [ ] Ensure proper error messages on leaks

### pkg/db tests
- [ ] Replace ad-hoc cleanup with CleanupTestDB()
- [ ] Add VerifyTestDBCleanup() after cleanup
- [ ] Ensure proper error messages on leaks

### pkg/juicefs tests
- [ ] Update to use new test helpers
- [ ] Add VerifyTestJuiceFSCleanup() after cleanup
- [ ] Ensure proper error messages on leaks

### pkg/overlay tests
- [ ] Update to use new test helpers
- [ ] Add VerifyTestOverlayCleanup() after cleanup
- [ ] Ensure proper error messages on leaks

### pkg/services tests
- [ ] Replace ad-hoc cleanup with CleanupTestServices()
- [ ] Add VerifyTestServicesCleanup() after cleanup
- [ ] Ensure proper error messages on leaks

### server/system tests
- [ ] Update TestSystem() to use package verification helpers
- [ ] Remove ad-hoc verification code
- [ ] Ensure each component cleanup is verified
- [ ] Keep aggressive cleanup for test environment

## Phase 5: Validation

### Regression Testing
- [ ] Run full test suite with pkg/leaser changes
- [ ] Run full test suite with pkg/db changes
- [ ] Run full test suite with pkg/juicefs changes
- [ ] Run full test suite with pkg/overlay changes
- [ ] Run full test suite with pkg/services changes
- [ ] Run full system tests

### Resource Leak Testing
- [ ] Verify no loop devices leak (overlay tests)
- [ ] Verify no mounts leak (juicefs + overlay tests)
- [ ] Verify no processes leak (services + juicefs tests)
- [ ] Verify no file handles leak (db tests)
- [ ] Verify no S3 lease conflicts (leaser tests)

### Error Scenario Testing
- [ ] Test cleanup when setup fails
- [ ] Test cleanup when shutdown times out
- [ ] Test cleanup when resources are wedged
- [ ] Test multiple Start() calls (idempotency)
- [ ] Test multiple Stop() calls (idempotency)
- [ ] Test multiple Wait() calls (safety)
- [ ] Test Stop() + Wait() from multiple goroutines
- [ ] Test full restart cycle for each component
- [ ] Test strict ordering preserved under failures

### Documentation Review
- [ ] Verify error messages are helpful
- [ ] Verify diagnostics suggest debugging steps
- [ ] Verify all public APIs documented
- [ ] Update package READMEs if needed

## Optional: Server/System Interface

- [ ] Define SystemComponent interface in server/system
- [ ] Define ExternalResourceManager interface
- [ ] Update components to note they implement interface (doc comment)
- [ ] Do NOT make components depend on server/system types

## Final Verification

- [ ] All tests pass
- [ ] No resource leaks in test suite
- [ ] Error messages are clear and actionable
- [ ] All New() functions do NO setup
- [ ] All Start() methods follow strict internal ordering
- [ ] All Start() methods are idempotent
- [ ] All Stop() methods are idempotent
- [ ] All components are restartable (Start → Stop → Start works)
- [ ] Stop() reverses the order of Start()
- [ ] System startup sequence unchanged
- [ ] System shutdown sequence unchanged
- [ ] Critical internal orders preserved (lease→litestream, loop→ext4→overlay, logdir→db)
- [ ] Critical timeouts preserved (5min JuiceFS, 1min Litestream)
- [ ] All test helpers are exported and documented
- [ ] Code review completed
- [ ] README updated if needed

## Notes

- Work on ONE component at a time
- Run full test suite after each component
- Commit after each phase per component
- Keep backward compatibility until Phase 4
- Do NOT change setup logic - New() functions stay minimal
- Do NOT change internal startup order - lease before litestream, loop before overlay, etc.
- Do NOT add timeouts to cleanup methods
- Do NOT change system-level shutdown sequence in system/
- Ensure components are truly restartable - test Start() → Stop() → Start()

## Key Design Rules (from pkg/leaser implementation)

### Lifecycle
1. **Start() errors if already started** - NOT idempotent, returns error to catch programming bugs
2. **Stop() IS idempotent** - can be called multiple times safely
3. **No mutex/atomic for simple flags** - just use plain bool, document expected usage
4. **Components are restartable** - Start() → Stop() → Start() works (channels recreated)

### Resource Verification (Simplified)
5. **Two simple slices, no interfaces**:
   ```go
   setupVerifiers   []func(context.Context) error  // verify resources exist
   cleanupVerifiers []func(context.Context) error  // verify resources cleaned up
   ```
6. **Verifiers check ONLY system state** - filesystem, /proc/mounts, /proc/<pid>, losetup -a, etc.
7. **Do NOT track internal Go values** - unless they directly represent external resources
8. **No VerifySetup/VerifyCleanup methods** - tests call verifiers directly in loops
9. **Verifiers cleared in Start()** - each run starts fresh
10. **SetupVerifiers() and CleanupVerifiers()** - simple getters returning the slices
11. **If resource doesn't need cleanup check** - only add setup verifier (S3 objects, persistent files, etc.)

### Adding Verifiers
```go
// In Start(), as each resource is acquired:
m.setupVerifiers = append(m.setupVerifiers, func(ctx context.Context) error {
    // Check filesystem, /proc, etc.
    return nil
})
m.cleanupVerifiers = append(m.cleanupVerifiers, func(ctx context.Context) error {
    // Check resource is gone
    return nil
})
```

### Using Verifiers in Tests
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
