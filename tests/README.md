# Sprite Integration Tests

This directory contains integration tests for the Sprite deployment and functionality.

## Prerequisites

1. Fly.io account and authenticated CLI (`flyctl`)
2. Docker installed and running
3. Go 1.21 or later
4. Environment variables:
   - `FLY_APP_NAME`: Your Fly.io app name
   - `SPRITE_TOKEN`: Authentication token for the Sprite API (see below)
   - `FLY_API_TOKEN` (optional): Fly API token; will use `flyctl auth token` if not set

### Obtaining the Sprite API token

When you deploy the Sprite environment (e.g. via `go run ../cmd/deploy.go` or `make build && make deploy`),
the machine configuration (in `cmd/machine-config.json`) contains the HTTP API token under the
`SPRITE_HTTP_API_TOKEN` field. You can extract and export it locally (using `jq`) before running tests:

```bash
export SPRITE_TOKEN=$(jq -r '.containers[0].env.SPRITE_HTTP_API_TOKEN' cmd/machine-config.json)
```

If you prefer, you can copy the token value manually from `cmd/machine-config.json`, or use a custom
show command to retrieve it from the deployed machine.

## Running the Tests

### Full Integration Test

This test will:
1. Deploy the sprite to a Fly machine
2. Build the sprite client binary
3. Test basic exec commands
4. Test zombie process cleanup
5. Test checkpoint/restore functionality

```bash
# Set required environment variables
export FLY_APP_NAME=your-app-name
export SPRITE_TOKEN=your-sprite-token

# Run the integration test (using Makefile - recommended)
make test

# Or run directly with go test (requires GOWORK=off)
GOWORK=off go test -v -timeout 10m
```

**Note:** `GOWORK=off` is required because the project uses Go workspaces. The Makefile targets automatically set this.

### Individual Test Components

You can also run individual test components:

```bash
# Using Makefile (recommended)
make test-deploy      # Just test deployment
make test-zombie      # Just test zombie cleanup
make test-checkpoint  # Just test checkpoint/restore

# Or using go test directly
GOWORK=off go test -v -run TestDeployAndFunctionality/Deploy
GOWORK=off go test -v -run TestDeployAndFunctionality/ZombieCleanup
GOWORK=off go test -v -run TestDeployAndFunctionality/CheckpointRestore
```

## What the Tests Do

### 1. Deployment Test
- Builds and pushes the Docker image
- Creates or updates a Fly machine with the sprite
- Waits for the machine to reach "started" state
- Handles stuck states by force-deleting and exiting with error

### 2. Client Build Test
- Builds the sprite client to `../dist/sprite`
- Verifies the binary was created successfully

### 3. Basic Commands Test
- Tests `sprite exec` with simple echo commands
- Tests file creation and verification

### 4. Zombie Cleanup Test
- Uses the `/debug/create-zombie` endpoint to create a zombie process
- Verifies the process is initially a zombie
- Waits and verifies that the sprite's init system cleans it up

### 5. Checkpoint/Restore Test
- Creates a file with unique content
- Creates a checkpoint
- Modifies the file
- Restores from the checkpoint
- Verifies the file content is restored

## Debugging

If tests fail, you can:
1. Check the deploy output for errors
2. Use `flyctl logs -a $FLY_APP_NAME` to see sprite logs
3. Use `flyctl ssh console -a $FLY_APP_NAME` to inspect the machine
4. The test keeps the deployment running by default for debugging

## Cleanup

The test does not automatically clean up the deployment. To remove it:

```bash
flyctl machine destroy -a $FLY_APP_NAME --force
```

Or uncomment the cleanup code in `cleanupDeployment()` function. 