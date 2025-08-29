# leaser

The leaser package provides a distributed lease management system using S3 (or compatible) object storage with optimistic concurrency control via ETags.

## Features

- **Optimistic lease acquisition**: Attempts to claim a lease without reading first
- **ETag-based concurrency control**: Uses S3 ETags for atomic compare-and-swap operations
- **Automatic lease refresh**: Keeps leases alive while the holder is running
- **Refresh count tracking**: Tracks how many times a lease has been refreshed
- **Graceful failure handling**: Handles machine crashes and network partitions
- **No external dependencies**: Uses only S3 object storage for coordination
- **Fly.io optimization**: Special behavior for faster failover in Fly.io environments

## Lease Duration

- **Lease duration**: 15 minutes
- **Refresh interval**: 5 minutes

This provides a 10-minute buffer for temporary network issues while allowing relatively quick failover when instances crash.

## Refresh Count Tracking

The leaser tracks how many times a lease has been refreshed since it was first acquired. This information is:
- Stored in the lease record in S3
- Incremented on each successful refresh
- Reset to 0 when a new lease is acquired
- Preserved when taking over another machine's lease

This can be useful for:
- Monitoring lease stability
- Detecting lease flapping
- Debugging distributed system behavior

## Fly.io Environment

When running in Fly.io (detected by `FLY_MACHINE_ID` environment variable), the leaser has special behavior to enable faster failover:

1. **Single instance detection**: Uses DNS lookup on `{FLY_APP_NAME}.internal` to check if this is the only instance
2. **Faster takeover**: If we're the only instance and the current lease hasn't been refreshed in >5 minutes, we can take it over immediately instead of waiting for expiration
3. This reduces failover time from up to 15 minutes to just 5 minutes when other instances crash

## Usage

```go
import "github.com/sprite-env/packages/leaser"

// Create configuration
config := leaser.Config{
    BaseDir:           "/var/sprite",
    S3AccessKey:       "your-access-key",
    S3SecretAccessKey: "your-secret-key", 
    S3EndpointURL:     "https://s3.amazonaws.com",
    S3Bucket:          "your-bucket",
}

// Create lease manager
lm, err := leaser.New(config)
if err != nil {
    log.Fatal(err)
}
defer lm.Stop()

// Wait for lease acquisition
ctx := context.Background()
if err := lm.Wait(ctx); err != nil {
    log.Fatal("Failed to acquire lease:", err)
}

// Check attempt count (useful for slow start logic)
if lm.LeaseAttemptCount() > 1 {
    // Lease required multiple attempts, may want to restore from backup
}

// Check refresh count (useful for monitoring)
refreshCount := lm.RefreshCount()
log.Printf("Lease refresh count: %d", refreshCount)

// Lease is now held and will be automatically refreshed
```

## How It Works

1. **Optimistic Acquisition**: First attempts to create/update the lease object using the last known ETag (stored locally)
2. **Conflict Resolution**: If the optimistic attempt fails:
   - Reads the current lease to check if it's expired or held by the same machine
   - If expired or same machine, acquires with the current ETag
   - If held by another machine, waits with exponential backoff
   - In Fly.io: Also checks if we're the only instance for faster takeover
3. **Automatic Refresh**: Once acquired, the lease is refreshed every 5 minutes
4. **Local State**: Stores the last successful ETag locally for fast reacquisition on restart

## Testing

The package includes comprehensive tests using mock S3 clients. Run tests with:

```bash
cd packages/leaser
go test -v
```