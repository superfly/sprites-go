# Sprite Deploy Utilities

A collection of utilities for managing Sprite environments on Fly.io:
- `deploy.go` - Deploy Docker images with volume and machine management
- `show.go` - Display machine information and configuration
- `exec.go` - Execute commands remotely via the Sprite API

## Prerequisites

- Docker installed and running
- `flyctl` CLI installed and authenticated
- Go 1.21+ (for building)

## Usage

```bash
# From the cmd directory
go run deploy.go -a YOUR_APP_NAME

# Or with environment variable
FLY_APP_NAME=YOUR_APP_NAME go run deploy.go

# Build and run
go build deploy.go
./deploy -a YOUR_APP_NAME

# Skip build and just push
./deploy -a YOUR_APP_NAME -skip-build
```

## What it does

1. Builds the Docker image from the root Dockerfile
2. Tags it as `registry.fly.io/<app-name>:latest`
3. Authenticates with Fly's Docker registry via `flyctl auth docker`
4. Pushes the image
5. Creates or finds a volume named `sprite_data` (10GB in ord region)
6. Creates or updates a machine named `sprite_compute`
7. Deploys using the configuration from `machine-config.json`

## Environment Variables

- `FLY_APP_NAME`: Alternative to `-a` flag

## Implementation Details

This is a hacky utility that uses `flyctl` commands directly via shell execution rather than using the Fly Go SDK. This makes it simpler and avoids API compatibility issues.

## Notes

- The utility uses the `machine-config.json` template and replaces `<volume_id>` and `<image_ref>` placeholders
- Ubuntu base image references in the config are preserved as-is
- The deployment region is hardcoded to `ord`
- Assumes `flyctl` is authenticated (run `flyctl auth login` first)