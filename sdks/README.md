# Sprite SDK Testing Infrastructure

This directory contains the testing infrastructure for all Sprite SDKs.

## Structure

- `Dockerfile.test` - Docker image for running SDK tests
- `run-tests.sh` - Main test runner script that starts sprite server and runs all SDK tests
- `test-harness/` - Go-based integration test harness for testing SDK implementations
- `python/` - Python SDK implementation and tests

## Running Tests

To run all SDK tests:

```bash
make test-sdks
```

This will:
1. Build a Docker image with all SDK dependencies
2. Start a sprite server instance
3. Run tests for each SDK (currently Python)
4. Run the test harness against both the real sprite client and SDK CLI wrappers
5. Ensure all SDKs are tested against the same sprite instance

## Test Harness

The test harness (`test-harness/main.go`) is a Go program that tests common sprite client functionality:

- Basic command execution
- Working directory and environment variable support
- Exit codes and stdout/stderr handling
- Checkpoint operations (create, list)
- Admin commands

The harness can test any sprite client implementation by setting the `SPRITE_CLIENT_BINARY` environment variable.

## Adding New SDKs

To add tests for a new SDK:

1. Create a directory for your SDK (e.g., `sdks/javascript/`)
2. Add a `run-tests.sh` script in your SDK directory
3. Update `sdks/run-tests.sh` to call your SDK's test script
4. If your SDK provides a CLI wrapper, test it with the harness

## Python SDK

The Python SDK includes:
- Full sprite API client implementation
- Comprehensive unit and integration tests
- CLI wrapper (`sprite-cli`) for command-line usage
- Flexible datetime parsing for various ISO 8601 formats

### Key Features

- Simplified checkpoint/restore operations (returns boolean success)
- WebSocket-based command execution with streaming I/O
- TTY support for interactive commands
- Parallel command execution support

## Environment Variables

- `SPRITE_URL` - Sprite server URL (required)
- `SPRITE_TOKEN` - Authentication token (required)
- `SPRITE_ADMIN_TOKEN` - Admin authentication token (optional, falls back to SPRITE_TOKEN)