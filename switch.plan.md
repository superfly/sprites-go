# Switch checkpoint/suspend from fsfreeze to cgroup.freeze

### What we'll change

- Replace filesystem-level `fsfreeze`/`unfreeze` with cgroup v2 `cgroup.freeze` on the sprite cgroup during checkpoint/suspend.
- Keep overlay syncs to ensure data integrity; overlay no longer handles any freeze/unfreeze.

### Where it happens today

- Filesystem freeze/unfreeze is done inside the overlay manager:
```530:537:pkg/overlay/mount.go
// 2) Freeze the underlying ext4 filesystem to prevent new writes
m.logger.Debug("Freezing underlying ext4 filesystem", "path", m.mountPath)
freezeCmd := exec.Command("fsfreeze", "--freeze", m.mountPath)
if output, err := freezeCmd.CombinedOutput(); err != nil {
    return fmt.Errorf("failed to freeze ext4 filesystem: %w, output: %s", err, string(output))
}
```

```564:577:pkg/overlay/mount.go
m.logger.Debug("Unfreezing underlying ext4 filesystem", "path", m.mountPath)
unfreezeCmd := exec.Command("fsfreeze", "--unfreeze", m.mountPath)
if output, err := unfreezeCmd.CombinedOutput(); err != nil {
    // ... already-unfrozen check ...
    return fmt.Errorf("failed to unfreeze ext4 filesystem: %w, output: %s", err, string(output))
}
```

- System coordinates this during suspend via `SyncOverlay`:
```468:485:server/system/system.go
// This will:
// 1. Sync the overlayfs filesystem (flush pending writes)
// 2. Freeze the underlying ext4 filesystem
// 3. Sync the loopback mount and fsync the image file
if err := s.OverlayManager.PrepareForCheckpoint(ctx); err != nil {
    return nil, fmt.Errorf("failed to prepare overlay for suspension: %w", err)
}
// Return the unfreeze function to be called after resume
unfreezeFunc := func() error {
    s.logger.Debug("Unfreezing filesystem after resume")
    return s.OverlayManager.UnfreezeAfterCheckpoint(ctx)
}
```

### Proposed design (finalized per guidance)

1) Add freeze/thaw to pkg/resources.Manager (blocking writes)

- Implement on `pkg/resources.Manager`:
  - `Freeze(timeout time.Duration) error` → write "1" to `<cgroupPath>/cgroup.freeze`. No polling; rely on kernel blocking semantics.
  - `Thaw(timeout time.Duration) error` → write "0" to `<cgroupPath>/cgroup.freeze`.
- Operate on the existing Manager instance for the sprite cgroup (`/sys/fs/cgroup/containers`) created by `ResourceMonitor` (no PID lookups).
- Add a helper method on `ResourceMonitor` (or `MonitorGroup`) to expose the sprite Manager: `GetSpriteManager() *Manager`.

2) Simplify overlay sync (no freeze/unfreeze)

- In `pkg/overlay`, remove all `fsfreeze`/`unfreeze` calls and delete `UnfreezeAfterCheckpoint(ctx)`.
- Keep `PrepareForCheckpoint(ctx)` but make it sync-only:
  - `sync` overlayfs target if mounted
  - `m.sync(ctx)` loopback mount
  - `fsync` image file
- Update comments to reflect that this is now sync-only (no freezing).

3) Orchestrate in ActivityMonitor using ResourceMonitor

- In `server/system/activity_monitor.go: prepSuspend`:
  - Get the sprite cgroup manager: `spriteMgr := m.system.ResourceMonitor.GetSpriteManager()`
  - Call `spriteMgr.Freeze(5 * time.Second)` (blocking write) BEFORE overlay sync
  - Call `m.system.OverlayManager.PrepareForCheckpoint(ctx)` (now sync-only)
  - Append cleanup function that calls `spriteMgr.Thaw(5 * time.Second)`
  - This cleanup runs on BOTH cancel-before-suspend (activity detected) AND after resume
- Remove or simplify `System.SyncOverlay`:
  - Option 1: Delete it entirely, move overlay sync call directly into `prepSuspend`
  - Option 2: Make it a simple overlay-sync helper with no freeze/unfreeze semantics
- Adjust `server/api/suspend.go`:
  - If keeping this endpoint active: call overlay sync only (no freeze)
  - Let `ActivityMonitor` own the freeze/thaw lifecycle for steady-state suspends

4) Tests and validation

- Unit tests in `pkg/resources` for `Freeze`/`Thaw`:
  - Create temp test cgroup under `/sys/fs/cgroup` (skip if permissions missing)
  - Verify writes to `cgroup.freeze` succeed
  - Verify frozen state via `cgroup.events` (optional read check)
- Update overlay tests:
  - Remove expectations around `fsfreeze` command execution
  - Assert sync behavior only (overlayfs sync, loopback sync, fsync image)
- Add observability:
  - Log durations for freeze/thaw operations
  - Log overlay sync duration
  - Track metrics for suspend preparation time

### Notes

- Uses the existing sprite cgroup manager from `ResourceMonitor`; no new manager instances, no PID resolution, no polling.
- Ensure thaw occurs both on resume and when suspend is cancelled due to activity (via the common deferred cleanup).
- **New architecture context**: System now uses a unified service manager (`UnifiedServiceManager`) that handles boot/shutdown with dependency graphs. The container service is registered as a managed service that depends on overlay. This doesn't change our freeze/thaw design since:
  - Freezing happens at the cgroup level (all container PIDs), independent of the service manager
  - ActivityMonitor orchestrates freeze/thaw during suspend preparation (before calling Fly suspend API)
  - Service manager handles orderly start/stop but not runtime suspend/resume

### To-dos

- [ ] Add `Freeze`/`Thaw` methods to `pkg/resources.Manager` using blocking cgroup.freeze writes
- [ ] Add `GetSpriteManager()` helper on `ResourceMonitor` to expose the containers cgroup manager
- [ ] Remove `fsfreeze` calls from `pkg/overlay`; make `PrepareForCheckpoint` sync-only; delete `UnfreezeAfterCheckpoint`
- [ ] Update `ActivityMonitor.prepSuspend`: freeze sprite cgroup, sync overlay, defer thaw (runs on cancel AND resume)
- [ ] Simplify or remove `System.SyncOverlay`; adjust `server/api/suspend.go` to sync-only
- [ ] Add unit tests for `Freeze`/`Thaw` in `pkg/resources` and update overlay tests



