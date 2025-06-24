# JuiceFS Package

This package provides a Go wrapper for managing JuiceFS filesystems with integrated support for checkpoints, overlays, and quotas.

## Features

- **JuiceFS Mount Management**: Automatically mounts and manages JuiceFS filesystems
- **Checkpoint Support**: Create and restore filesystem snapshots
- **Overlay Filesystem**: Optional overlay filesystem support for container environments
- **Automatic Quota Management**: Applies a 10TB quota to the `/active/fs` directory
- **Litestream Integration**: Automatic metadata backup and replication

## Directory Structure

When mounted, JuiceFS creates the following directory structure:

```
/data/
├── active/
│   └── fs/          # Main working directory (10TB quota applied)
├── checkpoints/     # Stored checkpoints
└── root-upper/      # Overlay mount (if enabled)
```

## Quota Management

The package automatically applies a 10TB quota to the `/active/fs` directory:

- **On Initial Mount**: Quota is applied asynchronously after the filesystem is ready
- **After Restore**: Quota is reapplied when restoring from a checkpoint
- **Quota Size**: 10TB (10240 GiB)
- **Application**: Runs asynchronously to avoid blocking mount/restore operations

The quota ensures that the `/active/fs` directory cannot exceed 10TB of storage, providing predictable resource usage.

## Usage Example

```go
config := juicefs.Config{
    BaseDir:    "/var/lib/juicefs",
    LocalMode:  true,
    VolumeName: "my-volume",
}

jfs, err := juicefs.New(config)
if err != nil {
    return err
}

// Start JuiceFS (creates /active/fs and applies quota)
if err := jfs.Start(ctx); err != nil {
    return err
}

// Create a checkpoint
if err := jfs.Checkpoint(ctx, "checkpoint-1"); err != nil {
    return err
}

// Restore from checkpoint (reapplies quota)
if err := jfs.Restore(ctx, "checkpoint-1"); err != nil {
    return err
}
```

## Configuration

Key configuration options:

- `BaseDir`: Base directory for JuiceFS data and metadata
- `LocalMode`: Use local storage instead of S3
- `VolumeName`: Name of the JuiceFS volume
- `OverlayEnabled`: Enable overlay filesystem support

## Testing

Run the package tests:

```bash
cd packages/juicefs
go test -v
```

Integration tests require `juicefs` and `litestream` binaries to be available in PATH.