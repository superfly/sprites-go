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
    "access_key": {"$env": "S3_ACCESS_KEY"},
    "secret_key": {"$env": "S3_SECRET_KEY"},
    "endpoint": {"$env": "S3_ENDPOINT"}
  },
  
  "exec": {
    "wrapper_command": ["crun", "exec", "app"],
    "tty_wrapper_command": ["crun", "exec", "-t", "app"]
  }
}
```

Environment variables are substituted using `{"$env": "VAR_NAME"}` syntax.

See `config.example.json` for a complete example. 