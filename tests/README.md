# Sprite Environment Tests

This directory contains integration and unit tests for the sprite environment.

## Test Setup

The test environment closely mirrors the production Docker image:
- Same Ubuntu 25.04 base
- Same binaries (crun, litestream, juicefs)
- Live spritectl server running on port 8080
- Source code mounted via volume for testing
- Persistent container with cgroup host access

## Running Tests

### Run all tests (recommended)
```bash
make test
```

### Run specific package tests
```bash
make test ARGS="go test -v ./pkg/juicefs/..."
```

### Run integration tests only
```bash
make test ARGS="go test -v -run TestExecIntegration ./tests/..."
```

### Clean up test container
```bash
make test-clean
```

### Interactive debugging
```bash
# Connect to the persistent test container
docker exec -it sprite-test-container bash

# Or start a fresh container
docker run --rm -it --privileged --cgroupns=host -v "$PWD":/workspace sprite-env-tests bash
```

## Test Architecture

1. **Persistent Container**: Tests run in a persistent container (`sprite-test-container`) that stays running between test runs
2. **Dockerfile.test**: Creates a test image that mirrors production
3. **server-entrypoint.sh**: Runs the spritectl server in persistent mode
4. **test-entrypoint.sh**: Used for one-shot test runs
5. **run-tests.sh**: Runs all tests in sequence

The persistent container approach:
- First run creates and starts the container with the server
- Subsequent runs reuse the existing container (faster)
- Server rebuilds automatically on each container start
- Container has `--cgroupns=host` for full cgroup access
- Use `make test-clean` to remove the container

## Environment Variables

The test environment sets:
- `SPRITE_TEST_DOCKER=1`: Indicates tests are running in Docker
- `SPRITE_URL=http://localhost:8080`: Server URL for integration tests  
- `SPRITE_TOKEN=test-token-12345`: Authentication token for tests
