# Sprite Client

A simple command-line client for interacting with the Sprite Environment API.

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
# Simple command
sprite-client exec ls -la

# With working directory
sprite-client exec -dir /app echo "Hello from /app"

# With environment variables
sprite-client exec -env KEY=value,FOO=bar env

# With custom timeout
sprite-client exec -timeout 5s curl https://example.com

# Allocate a TTY
sprite-client exec -tty /bin/bash
```

### Create Checkpoint

Create a checkpoint of the current state:

```bash
sprite-client checkpoint my-checkpoint-id
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
sprite-client checkpoint backup-$(date +%Y%m%d)

# Run a script
sprite-client exec -dir /app ./run-tests.sh

# Check environment
sprite-client exec env | grep NODE

# Restore from checkpoint
sprite-client restore backup-20240115
```

## Exit Codes

The `exec` command preserves the exit code of the remote command. Other commands exit with:
- 0 on success
- 1 on error 