# Sprite SDK Test Suite

This directory contains comprehensive tests for the Sprite SDK Go client using the standard Go test framework. The tests are designed to verify the behavior of exec, TTY, streaming, and concurrency features against a real Sprites API endpoint.

## Architecture

The test suite consists of two components:

1. **Go Test Framework** - Standard Go tests that automatically create and manage test sprites (located in `sdks/test/`)
2. **`test-cli`** - A CLI tool that uses the Sprite SDK to execute commands on sprites (located in `sdks/go/test-cli/`)

The tests use the standard Go testing framework and automatically create unique sprites for each test run, ensuring isolation and preventing conflicts between test runs.

## Overview

The test suite uses the standard Go test framework and can be run against any Sprite instance. It tests critical functionality including:

1. **Stdout/stderr streaming** - Ensures output streams properly for exec commands
2. **Fast command handling** - Verifies fast running commands don't miss stdout
3. **Concurrent execution** - Tests 10 concurrent fast running commands don't miss stdout
4. **No hanging** - Ensures no exec calls hang indefinitely
5. **Stdin functionality** - Verifies stdin works properly
6. **TTY support** - Tests TTY functionality and allocation

## Prerequisites

- Go 1.21 or later
- A valid `SPRITES_TEST_TOKEN` environment variable
- Access to a Sprite instance for testing

## Building

```bash
make build
```

This builds the test-cli binary required for the tests:
- `test-cli` - The CLI tool that uses the Sprite SDK (in `sdks/go/test-cli/`)

## Running Tests

### Run All Tests

```bash
SPRITES_TEST_TOKEN=your_token SDK_TEST_COMMAND=../go/test-cli/test-cli make test-all
```

### Run a Specific Test

```bash
SPRITES_TEST_TOKEN=your_token SDK_TEST_COMMAND=../go/test-cli/test-cli TEST=TestStdoutStreaming make test
```

### Available Tests

- `TestStdoutStreaming` - Test stdout/stderr streaming
- `TestFastCommands` - Test fast running commands don't miss stdout
- `TestConcurrentCommands` - Test 10 concurrent fast running commands
- `TestNoHanging` - Test no exec calls hang
- `TestStdin` - Test stdin works properly
- `TestTTY` - Test TTY functionality

### Using Go Test Directly

You can also run tests directly with the Go test command:

```bash
# Run all tests
SPRITES_TEST_TOKEN=your_token SDK_TEST_COMMAND=../go/test-cli/test-cli go test -v

# Run a specific test
SPRITES_TEST_TOKEN=your_token SDK_TEST_COMMAND=../go/test-cli/test-cli go test -v -run TestStdoutStreaming

# Run with custom timeout
SPRITES_TEST_TOKEN=your_token SDK_TEST_COMMAND=../go/test-cli/test-cli go test -v -timeout 60s

# Run against a different API endpoint
SPRITES_BASE_URL=https://staging-api.sprites.dev SPRITES_TEST_TOKEN=your_token SDK_TEST_COMMAND=../go/test-cli/test-cli go test -v
```

### Environment Variables

- `SPRITES_TEST_TOKEN` - Authentication token (required)
- `SDK_TEST_COMMAND` - Path to the SDK test binary (required)
- `SPRITES_BASE_URL` - Base URL for the sprite API (optional, defaults to https://api.sprites.dev)

## Test Details

### Stdout Streaming Test
Verifies that both stdout and stderr are properly captured and streamed. Tests include:
- Basic stdout capture
- Stderr capture via combined output
- Proper newline handling

### Fast Commands Test
Ensures that very fast-running commands don't miss their output due to timing issues. Tests include:
- Single fast command execution
- Multiple sequential fast commands
- Output verification for each command

### Concurrent Commands Test
Tests the ability to handle multiple concurrent commands without losing output. Tests include:
- 10 concurrent echo commands
- Proper result collection and verification
- No missing or corrupted output

### No Hanging Test
Verifies that commands don't hang indefinitely and that timeouts work properly. Tests include:
- Normal command execution within timeout
- Proper timeout handling for long-running commands
- Context cancellation behavior

### Stdin Test
Tests stdin functionality for interactive commands. Tests include:
- Single line stdin input
- Multi-line stdin input
- Proper input/output correlation

### TTY Test
Verifies TTY allocation and functionality. Tests include:
- TTY-enabled command execution
- TTY device allocation verification
- TTY size configuration

## Integration with CI/CD

The test suite is designed to be easily integrated into CI/CD pipelines:

```bash
# In your CI pipeline
export SPRITES_TEST_TOKEN=your_ci_token
export SDK_TEST_COMMAND=../go/test-cli/test-cli
make test-all
```

### GitHub Actions

A GitHub Actions workflow is included that automatically tests the SDK:

- **Workflow file**: `.github/workflows/sdk-tests.yml`
- **Triggers**: Push/PR to main/go-sdk branches, manual dispatch
- **Required secrets**: `SPRITES_TEST_TOKEN`

The workflow:
1. Builds the Go SDK test binary (`sdks/go/test-cli/test-cli`)
2. Runs all tests using the standard Go test framework
3. Uploads test artifacts for debugging

## Troubleshooting

### Common Issues

1. **Authentication errors**: Ensure `SPRITES_TEST_TOKEN` is set and valid
2. **Sprite creation failures**: Check API connectivity and token permissions
3. **Timeout errors**: Increase the timeout value for slow networks
4. **Concurrent test failures**: May indicate resource limits or API rate limiting

### Debug Mode

Use the `-v` flag to see detailed output from each test:

```bash
SPRITES_TEST_TOKEN=your_token SDK_TEST_COMMAND=../go/test-cli/test-cli go test -v
```

## Contributing

When adding new tests:

1. Create a new test file following the pattern `*_test.go`
2. Use the `setupTestSprite(t)` helper function for sprite management
3. Update this README with test description
4. Update the Makefile help text if needed

## Architecture

The test suite is completely independent of the main project:
- Has its own `go.mod` file
- Uses a local replace directive to reference the SDK
- Can be built and run independently
- Designed for testing against real API endpoints
- Automatically creates and destroys unique sprites for each test run
