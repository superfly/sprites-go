# Sprite Client

A command-line client for interacting with the Sprite Environment API. The client uses Docker's multiplexed stream format by default for proper stdout/stderr separation.

## Building

```bash
go build -o sprite-client
```

## Configuration

The client requires two environment variables:

- `SPRITE_URL`: The base URL of the Sprite API (e.g., `http://localhost:8181` or `https://myapp.fly.dev`)
- `SPRITE_TOKEN`: The authentication token for the API

## Usage

### Execute Command

Execute a command in the sprite environment:

```bash
# Simple command (uses Docker stream format by default)
sprite-client exec ls -la

# With working directory
sprite-client exec -dir /app echo "Hello from /app"

# With environment variables
sprite-client exec -env KEY=value,FOO=bar env

# With custom timeout
sprite-client exec -timeout 5s curl https://example.com

# Allocate a TTY
sprite-client exec -tty /bin/bash

# Use legacy NDJSON format
sprite-client exec -no-docker-stream cat data.json
```

### Checkpoint Management

Create a checkpoint of the current state:

```bash
# Create a new checkpoint (can use checkpoint, checkpoints, or c)
sprite-client checkpoint create my-checkpoint-id
sprite-client checkpoints create my-checkpoint-id
sprite-client c create my-checkpoint-id

# List all checkpoints
sprite-client checkpoint list
sprite-client checkpoints list
sprite-client c list
```

### Restore from Checkpoint

Restore the system from a checkpoint:

```bash
sprite-client restore my-checkpoint-id
```

## Examples

```bash
# Set up environment
export SPRITE_URL=https://myapp.fly.dev
export SPRITE_TOKEN=mysecrettoken

# List files
sprite-client exec ls -la /data

# Create a checkpoint
sprite-client checkpoint create backup-$(date +%Y%m%d)

# List all checkpoints
sprite-client checkpoint list

# Run a script
sprite-client exec -dir /app ./run-tests.sh

# Check environment
sprite-client exec env | grep NODE

# Restore from checkpoint
sprite-client restore backup-20240115
```

## Exit Codes

- **With NDJSON format** (`-no-docker-stream`): The `exec` command preserves the exit code of the remote command
- **With Docker stream format** (default): Always returns 0 on success, 1 on stream error (exit codes are not transmitted in Docker's multiplexed protocol)
- Other commands exit with:
  - 0 on success
  - 1 on error

## Output Format

By default, the client uses Docker's multiplexed stream protocol, which properly separates stdout and stderr. This is the same format used by Docker when TTY is **not** allocated (i.e., when running without `-t`).

### Default Behavior (Docker Stream)

The client automatically demultiplexes stdout and stderr using the `github.com/moby/moby/pkg/stdcopy` package:

```bash
# Default: stdout and stderr are properly separated
sprite-client exec sh -c 'echo "This goes to stdout" && echo "This goes to stderr" >&2'

# With TTY: stdout/stderr are combined by the TTY itself
sprite-client exec -tty sh -c 'echo "stdout" && echo "stderr" >&2'
```

### NDJSON Format (Legacy)

If you need the legacy NDJSON format, use the `-no-docker-stream` flag:

```bash
# Use NDJSON format (each line is a JSON object)
sprite-client exec -no-docker-stream cat data.json
```

NDJSON format outputs each message as a JSON object with type, data, and timestamp:
```json
{"type":"stdout","data":"Hello world","time":"2024-01-01T12:00:00Z"}
{"type":"stderr","data":"Error message","time":"2024-01-01T12:00:01Z"}
{"type":"exit","exit_code":0,"time":"2024-01-01T12:00:02Z"}
```

### Benefits of Docker Stream (Default)

- **Binary-safe**: Handles binary data correctly
- **Proper separation**: Stdout and stderr remain separate
- **Standard compatibility**: Works with Docker tooling
- **Better performance**: Less overhead than JSON encoding