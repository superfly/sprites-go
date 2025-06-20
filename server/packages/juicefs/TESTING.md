# Testing JuiceFS Package

This document describes how to run tests for the JuiceFS package.

## Quick Start

```bash
# Run unit tests only
make test

# Run tests in Docker (includes integration tests)
make test-docker
```

## Test Targets

### `make test`
Runs unit tests by default. If JuiceFS and Litestream binaries are found in PATH, it will also run integration tests.

### `make test-unit`
Runs only unit tests. Does not require JuiceFS or Litestream binaries.

### `make test-integration`
Runs integration tests. Requires both JuiceFS and Litestream binaries to be installed.

### `make test-examples`
Runs example tests. Requires S3 environment variables:
- `SPRITE_S3_ACCESS_KEY`
- `SPRITE_S3_SECRET_ACCESS_KEY`
- `SPRITE_S3_ENDPOINT_URL`
- `SPRITE_S3_BUCKET`
- `SPRITE_WRITE_DIR`

### `make test-docker`
Runs all tests (including integration) in a Docker container with JuiceFS and Litestream pre-installed.

### `make coverage`
Runs tests and generates an HTML coverage report at `coverage.html`.

### `make clean`
Removes test artifacts and Docker images.

## Docker Testing

The `test-docker` target builds a Docker image with:
- Go 1.22
- JuiceFS v1.1.2
- Litestream v0.3.13
- FUSE support
- SQLite support

The Docker container runs with:
- `--privileged` flag for FUSE access
- `/dev/fuse` device access
- `SYS_ADMIN` capability

## Integration Tests

Integration tests are marked with the build tag `integration`:

```go
//go:build integration
// +build integration
```

They test actual JuiceFS operations including:
- Mounting filesystems
- Creating checkpoints
- Restoring from checkpoints
- Litestream replication

## Local Mode Testing

Tests can use local mode to avoid S3 dependencies:

```go
config := juicefs.Config{
    BaseDir:   t.TempDir(),
    LocalMode: true,
}
```

This creates a fully functional JuiceFS filesystem using local disk storage.

## Coverage

Current test coverage focuses on:
- Configuration validation
- Directory creation
- Litestream configuration generation
- Cache/buffer size calculations
- Ready detection
- Signal handling
- Channel-based synchronization

## Troubleshooting

### Tests fail with "juicefs binary not found"
Install JuiceFS:
```bash
wget https://github.com/juicedata/juicefs/releases/download/v1.1.2/juicefs-1.1.2-linux-amd64.tar.gz
tar -xzf juicefs-1.1.2-linux-amd64.tar.gz
sudo mv juicefs /usr/local/bin/
```

### Tests fail with "litestream binary not found"
Install Litestream:
```bash
wget https://github.com/benbjohnson/litestream/releases/download/v0.3.13/litestream-v0.3.13-linux-amd64.tar.gz
tar -xzf litestream-v0.3.13-linux-amd64.tar.gz
sudo mv litestream /usr/local/bin/
```

### Docker tests fail with FUSE errors
Ensure Docker is running with proper permissions:
- Docker Desktop: Enable "Privileged" in settings
- Linux: Run Docker daemon with appropriate permissions