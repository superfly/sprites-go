# Checkpoint Module Refactoring

## Overview

The checkpoint functionality has been extracted from `juicefs.go` into a separate `CheckpointManager` module to improve code organization and maintainability.

## Changes Made

### New Files
1. **checkpoint_manager.go** - Contains all checkpoint and restore logic
2. **checkpoint_manager_test.go** - Tests for the checkpoint manager

### Architecture

```
JuiceFS
  └── CheckpointManager
       └── CheckpointDB
```

The `JuiceFS` struct now delegates all checkpoint operations to the `CheckpointManager`, which internally manages the `CheckpointDB`.

### Benefits
- **Reduced complexity**: `juicefs.go` reduced from 989 to 841 lines (15% reduction)
- **Better separation of concerns**: Checkpoint logic is isolated in its own module
- **Easier testing**: Checkpoint functionality can be tested independently
- **Cleaner API**: Simple delegation pattern from JuiceFS to CheckpointManager

### API

The public API remains unchanged:
```go
func (j *JuiceFS) Checkpoint(ctx context.Context, checkpointID string) error
func (j *JuiceFS) Restore(ctx context.Context, checkpointID string) error
```

### CheckpointManager Interface

```go
type CheckpointManager struct {
    baseDir    string
    db         *CheckpointDB
    overlayMgr *OverlayManager
}

func NewCheckpointManager(baseDir string, overlayMgr *OverlayManager) *CheckpointManager
func (cm *CheckpointManager) Initialize(mountPath string) error
func (cm *CheckpointManager) Close() error
func (cm *CheckpointManager) Checkpoint(ctx context.Context, checkpointID string) error
func (cm *CheckpointManager) Restore(ctx context.Context, checkpointID string) error
```

### Integration

The `JuiceFS` struct integrates the checkpoint manager:
1. Creates `CheckpointManager` in `New()`
2. Initializes database in `watchForReady()`
3. Closes manager in `monitorProcess()`
4. Delegates `Checkpoint()` and `Restore()` calls

This refactoring makes the codebase more modular and maintainable while preserving all existing functionality.