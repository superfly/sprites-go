# JuiceFS Package

This package provides a Go implementation of the JuiceFS component logic that was previously implemented in Bash scripts.

## Features

- Automatic JuiceFS filesystem initialization and mounting
- Litestream replication for metadata backup (S3 or local disk)
- Automatic restoration from backup on startup
- Checkpoint and restore functionality
- Ready detection via stderr monitoring
- Graceful shutdown with unmounting
- **Local mode** for testing without S3 dependencies

## Usage

### S3 Mode (Production)

```go
import "github.com/fly-dev-env/sprite-env/server/packages/juicefs"

// Create configuration
config := juicefs.Config{
    BaseDir:           "/workspace/juicefs",
    S3AccessKey:       os.Getenv("SPRITE_S3_ACCESS_KEY"),
    S3SecretAccessKey: os.Getenv("SPRITE_S3_SECRET_ACCESS_KEY"),
    S3EndpointURL:     os.Getenv("SPRITE_S3_ENDPOINT_URL"),
    S3Bucket:          os.Getenv("SPRITE_S3_BUCKET"),
    VolumeName:        "juicefs", // optional, defaults to "juicefs"
}

// Create JuiceFS instance
jfs, err := juicefs.New(config)
if err != nil {
    log.Fatal(err)
}

// Start JuiceFS (blocks until ready or error)
ctx := context.Background()
if err := jfs.Start(ctx); err != nil {
    log.Fatal(err)
}

// JuiceFS is now mounted and ready
// The active directory is at: {BaseDir}/data/active/fs

// Create a checkpoint
if err := jfs.Checkpoint(ctx, "checkpoint-1"); err != nil {
    log.Printf("Failed to create checkpoint: %v", err)
}

// Restore from a checkpoint
if err := jfs.Restore(ctx, "checkpoint-1"); err != nil {
    log.Printf("Failed to restore: %v", err)
}

// Stop JuiceFS gracefully
if err := jfs.Stop(ctx); err != nil {
    log.Printf("Failed to stop: %v", err)
}
```

### Local Mode (Testing/Development)

```go
// Local mode configuration - no S3 required
config := juicefs.Config{
    BaseDir:    "/tmp/juicefs-test",
    LocalMode:  true,
    VolumeName: "test-volume",
}

jfs, err := juicefs.New(config)
// ... same usage as above
```

## Directory Structure

### S3 Mode
```
{BaseDir}/
├── cache/          # JuiceFS cache directory
├── metadata.db     # SQLite metadata database
└── data/           # Mount point
    ├── active/     # Active working directory
    │   └── fs/     # User data directory
    └── checkpoints/ # Checkpoint storage
```

### Local Mode
```
{BaseDir}/
├── cache/          # JuiceFS cache directory
├── local/          # Local storage backend (replaces S3)
├── litestream/     # Local litestream backups
├── metadata.db     # SQLite metadata database
└── data/           # Mount point
    ├── active/     # Active working directory
    │   └── fs/     # User data directory
    └── checkpoints/ # Checkpoint storage
```

## Key Differences from Bash Implementation

1. **No separate ready script**: The Go implementation monitors JuiceFS stderr output directly in a goroutine
2. **Integrated Litestream management**: Uses the supervisor package to manage the Litestream process
3. **Error handling**: Returns structured errors instead of exit codes
4. **Context support**: All operations support context for cancellation
5. **Channel-based synchronization**: Uses channels instead of mutexes for goroutine coordination
6. **Local mode support**: Can run entirely on local disk without S3 for testing
7. **Signal handling**: Properly handles SIGTERM and SIGINT for graceful shutdown
8. **Process execution order**: 
   - Go version starts Litestream first, then JuiceFS (more logical)
   - Bash version starts JuiceFS in background, then Litestream in foreground
9. **Bug fixes from bash version**:
   - Fixed undefined `$CACHE_DIR` variable (should be `$JUICEFS_CACHE_DIR`)
   - Fixed missing SQL query in bucket detection
   - Fixed unreachable wait statement after foreground litestream

## Dependencies

- `juicefs` binary must be available in PATH
- `litestream` binary must be available in PATH
- SQLite3 driver for Go (github.com/mattn/go-sqlite3)

This is a standalone module with no dependencies on other sprite-env packages.

## Testing

Tests can use local mode with temporary directories:

```go
func TestJuiceFS(t *testing.T) {
    tmpDir := t.TempDir()
    
    config := juicefs.Config{
        BaseDir:   tmpDir,
        LocalMode: true,
    }
    
    jfs, err := juicefs.New(config)
    // ... run tests
}
```