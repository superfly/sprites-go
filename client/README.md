# Sprite Client

The Sprite client allows you to manage and interact with sprites (lightweight VMs) across different organizations.

## Current Status

> **Note:** Sprites must be explicitly created using `sprite create` before they can be used. The client will not automatically create sprites.

## Configuration

The client uses two types of configuration:

### Global Configuration (~/.sprites/config.json)

Stores your organizations and their credentials:
- Organization names, URLs, and tokens
- Available sprites per organization
- Default organization and sprite

This file is automatically created and managed when you run `sprite org auth`.

### Local Configuration (.sprite)

Each directory can have a `.sprite` file that remembers the last organization and sprite used in that directory:

```json
{
  "organization": "default-1735676400",
  "sprite": "my-app"
}
```

This file is automatically created when you run sprite commands in a directory. The client will look for `.sprite` files in the current directory and parent directories to determine context.

Add `.sprite` to your `.gitignore` as it contains user-specific context.

## Environment Variables

### For Backward Compatibility
The client supports these environment variables for backward compatibility with direct sprite connections:
- `SPRITE_URL`: The sprite server URL
- `SPRITE_TOKEN`: Authentication token

When these are set, they take precedence over the configuration files.

### API Configuration
- `SPRITES_API_URL`: Override the default Sprites API URL (default: https://api.sprites.dev)

This is useful for testing or using alternative Sprites API endpoints:
```bash
export SPRITES_API_URL=https://staging.api.sprites.dev
sprite exec ls
```

## Building

```bash
go build -o sprite-client
```

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

### Port Forwarding (Proxy)

Forward local ports through the remote server's proxy:

```bash
# Forward a single port
sprite-client proxy 8080

# Forward multiple ports
sprite-client proxy 8080 3000 5432

# This will:
# - Listen on localhost:8080, localhost:3000, and localhost:5432
# - Forward connections through the remote server to its localhost on the same ports
```

This is useful for accessing services running in the sprite environment from your local machine.

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