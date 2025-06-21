# sprite-env

Sprite-env is a process supervisor with component management and state machine orchestration.

## Installation

### Download Pre-built Binaries

Download the latest release from [GitHub Releases](https://github.com/YOUR_ORG/YOUR_REPO/releases):

```bash
# Linux AMD64
curl -L https://github.com/YOUR_ORG/YOUR_REPO/releases/latest/download/sprite-env-linux-amd64.tar.gz | tar xz

# Linux ARM64
curl -L https://github.com/YOUR_ORG/YOUR_REPO/releases/latest/download/sprite-env-linux-arm64.tar.gz | tar xz

# macOS Intel
curl -L https://github.com/YOUR_ORG/YOUR_REPO/releases/latest/download/sprite-env-darwin-amd64.tar.gz | tar xz

# macOS Apple Silicon
curl -L https://github.com/YOUR_ORG/YOUR_REPO/releases/latest/download/sprite-env-darwin-arm64.tar.gz | tar xz
```

### Build from Source

```bash
# Build for current platform
make build

# Build release binaries for all platforms
make release-all

# Build specific platform
make release-linux-amd64
make release-linux-arm64
make release-darwin-amd64
make release-darwin-arm64
```

## Usage

```bash
# Using command-line arguments
./sprite-env -components-dir ./components -listen :8080 -- /path/to/supervised-process

# Using config file
./sprite-env -config config.json

# Mix both
./sprite-env -config config.json -components-dir ./components -- myapp
```

## Configuration

Sprite-env accepts a JSON config file with environment variable substitution:

```json
{
  "log_level": "info",
  "api_listen_addr": ":8080",
  
  "process_command": ["/app/myservice", "--port", "3000"],
  "process_graceful_shutdown_timeout": "30s",
  
  "components": {
    "db": {
      "start_command": ["/scripts/db/start.sh"],
      "ready_command": ["/scripts/db/ready.sh"]
    }
  },
  
  "s3": {
    "access_key": {"$env": "SPRITE_S3_ACCESS_KEY"},
    "secret_key": {"$env": "SPRITE_S3_SECRET_ACCESS_KEY"},
    "endpoint": {"$env": "SPRITE_S3_ENDPOINT_URL"}
  },
  
  "exec": {
    "wrapper_command": ["crun", "exec", "app"],
    "tty_wrapper_command": ["crun", "exec", "-t", "app"]
  }
}
```

Environment variables are substituted using `{"$env": "VAR_NAME"}` syntax.

See `config.example.json` for a complete example. 

## Running as PID 1 (Init Process)

When sprite-env runs as PID 1 (in containers or VMs), it automatically handles zombie process reaping. This is essential because:

1. PID 1 has special responsibilities in Unix/Linux systems
2. It becomes the parent of all orphaned processes
3. It must reap zombie processes to prevent resource exhaustion

### Zombie Reaping

When running as PID 1, sprite-env:
- Automatically detects if it's running as PID 1
- Sets up a SIGCHLD signal handler
- Reaps all zombie processes using `wait4()` with `WNOHANG`
- Logs reaped processes at debug level

This ensures that orphaned processes don't accumulate as zombies, which could eventually exhaust the process table.

#### Safety Guarantees

The zombie reaper is designed to be completely safe:
- **Non-blocking**: Uses `WNOHANG` flag with `wait4()`, so it never blocks
- **Clean shutdown**: Responds to context cancellation and exits cleanly
- **Resource cleanup**: Properly unregisters signal handlers on exit
- **Graceful termination**: The main process waits (with 1-second timeout) for the reaper to finish during shutdown
- **No hangs**: Cannot prevent the process from exiting since `wait4()` is non-blocking

### Example Container Usage

```dockerfile
FROM ubuntu:latest
COPY sprite-env /usr/local/bin/
# sprite-env will run as PID 1 and handle zombie reaping
ENTRYPOINT ["/usr/local/bin/sprite-env"]
CMD ["--config", "/etc/sprite-env/config.json"]
```

If you're using an init system like s6-overlay, tini, or dumb-init, they will handle zombie reaping instead, and sprite-env's reaper will automatically disable itself. 

## API Endpoints

### Main Endpoints

- `POST /checkpoint` - Create a checkpoint of the current state
- `POST /restore` - Restore from a checkpoint
- `POST /exec` - Execute a command in the context of the supervised process

### Debug Endpoints

The server provides debug endpoints for testing zombie reaping functionality when running as PID 1:

- `POST /debug/create-zombie` - Creates a zombie process for testing
- `GET /debug/check-process?pid=<PID>` - Checks if a process exists and its zombie status

#### Testing Zombie Reaping

A test script is provided at `server/tests/test_zombie_reaping.sh` to verify zombie reaping works correctly:

```bash
# Set your API token
export SPRITE_HTTP_API_TOKEN="your-token"

# Run the test (in an environment where sprite-env is PID 1)
./server/tests/test_zombie_reaping.sh
```

The test will:
1. Create a zombie process using the debug endpoint
2. Wait for automatic reaping via SIGCHLD
3. Verify the zombie was reaped
4. Check process status using the debug endpoint

These debug endpoints are only intended for testing and should not be exposed in production environments. 

# Sprite Control Server (spritectl)

The Sprite Control Server provides a REST API and process management capabilities for the Sprite environment.

## Features

- Process supervision with graceful shutdown
- JuiceFS integration for persistent storage
- HTTP API for remote command execution
- Checkpoint and restore functionality
- Automatic zombie process reaping when running as PID 1
- S3-backed or local storage options

## Environment Variables

### Required
- `SPRITE_HTTP_API_TOKEN` - Authentication token for the HTTP API (required when API server is enabled)
- `SPRITE_WRITE_DIR` - Base directory for writable data (usually `/dev/fly_vol`)

### S3 Storage (when not using local mode)
- `SPRITE_S3_ACCESS_KEY` - S3 access key
- `SPRITE_S3_SECRET_ACCESS_KEY` - S3 secret access key
- `SPRITE_S3_ENDPOINT_URL` - S3 endpoint URL
- `SPRITE_S3_BUCKET` - S3 bucket name
- `SPRITE_S3_REGION` - S3 region (optional, defaults to "us-east-1")

### Optional
- `SPRITE_LOCAL_MODE` - Set to "true" to use local storage instead of S3
- `SPRITE_KEEP_ALIVE_ON_ERROR` - Set to "true" to keep the server running when the supervised process fails (useful for debugging)

## Command Line Options

```bash
spritectl [options] [-- command args...]
```

### Options
- `-config <file>` - JSON configuration file
- `-debug` - Enable debug logging
- `-log-json` - Output logs in JSON format
- `-listen <addr>` - API server listen address (default from config)
- `-graceful-shutdown-timeout <duration>` - Process graceful shutdown timeout (default: 30s)
- `-juicefs-dir <path>` - JuiceFS base directory (overrides SPRITE_WRITE_DIR)
- `-version` - Show version and exit

### Examples

```bash
# Run with a Node.js application
spritectl -- node app.js

# Run with custom API port
spritectl -listen :8080 -- python server.py

# Run with debug logging
spritectl -debug -- ./my-app

# Use local storage mode
SPRITE_LOCAL_MODE=true spritectl -- ./my-app

# Keep server running on process failure (for debugging)
SPRITE_KEEP_ALIVE_ON_ERROR=true spritectl -- ./problematic-app
```

## API Endpoints

### POST /exec
Execute a command in the container environment.

### POST /checkpoint
Create a checkpoint of the current state.

### POST /restore
Restore from a checkpoint.

### GET /debug/create-zombie
Create a zombie process for testing (debug endpoint).

### GET /debug/check-process
Check if a process exists and its status.

## Process Management

The server supervises a single main process and handles:
- Graceful shutdown with configurable timeout
- Signal forwarding (SIGTERM, SIGINT, etc.)
- Automatic restart on restore operations
- Zombie process reaping when running as PID 1

## Configuration File

The `-config` option accepts a JSON file with the following structure:

```json
{
  "log_level": "info",
  "log_json": false,
  "api_listen_addr": "0.0.0.0:7778",
  "process_command": ["/app/start.sh"],
  "process_working_dir": "/app",
  "process_environment": ["NODE_ENV=production"],
  "exec_wrapper_command": ["crun", "exec", "app"],
  "exec_tty_wrapper_command": ["crun", "exec", "-t", "app"]
}
```

## Building

```bash
cd server
go build -o spritectl .
```

## Testing

```bash
make test
``` 