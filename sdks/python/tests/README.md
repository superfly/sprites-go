# Sprites Python SDK Tests

This directory contains unit and integration tests for the Sprites Python SDK.

## Structure

- `test_unit.py` - Unit tests that mock external dependencies
- `test_integration.py` - Integration tests that require a running Sprites server

## Running Tests

### Prerequisites

1. Build the server binary first:
   ```bash
   # From the project root
   make build
   ```

2. Install test dependencies:
   ```bash
   # From sdks/python/
   pip install -e ".[test]"
   # or
   make dev-install
   ```

### Running All Tests

```bash
# From sdks/python/
make test
```

### Running Unit Tests Only

Unit tests run quickly and don't require any external services:

```bash
make test-unit
# or
pytest tests/test_unit.py
```

### Running Integration Tests

Integration tests require the Sprites server binary:

```bash
# Run all integration tests
make test-integration

# Run only basic integration tests (skip TTY and checkpoint tests)
make test-integration-basic

# Run only TTY tests
make test-tty

# Run only checkpoint/restore tests (requires JuiceFS)
make test-checkpoint

# Or run directly with pytest
SPRITE_SERVER_BINARY=../../dist/server pytest tests/test_integration.py
```

### Running Tests in Docker

This is the most reliable way to run tests as it ensures a consistent environment with all dependencies:

```bash
# From sdks/python/
make test-docker
```

The Docker environment includes:
- JuiceFS for checkpoint/restore functionality
- Proper TTY allocation for TTY mode tests
- All required system dependencies

## Test Configuration

- `pytest.ini` - Pytest configuration
- Tests have a 60-second timeout by default
- The integration test server runs on port 28080

## Writing Tests

### Unit Tests

Unit tests should:
- Mock all external dependencies (WebSocket, HTTP requests)
- Test individual components in isolation
- Run quickly (< 1 second per test)

Example:
```python
def test_client_initialization():
    client = SpritesClient(token="test-token")
    assert client.token == "test-token"
```

### Integration Tests

Integration tests should:
- Use the real server binary
- Test end-to-end functionality
- Clean up after themselves

Example:
```python
def test_command_execution(sprite):
    result = sprite.exec("echo 'Hello'").run()
    assert result.returncode == 0
    assert result.stdout.decode().strip() == "Hello"
```

## Debugging Failed Tests

1. Run with verbose output:
   ```bash
   pytest -vv tests/test_integration.py::test_name
   ```

2. Check server logs:
   - Integration tests capture server stdout/stderr
   - Failed tests will show server output

3. Run a specific test:
   ```bash
   pytest tests/test_integration.py::TestBasicExecution::test_simple_echo
   ```

## Known Issues

- Checkpoint/restore tests require JuiceFS to be properly configured
  - In Docker, these tests should work automatically
  - Locally, you need to set up JuiceFS with appropriate environment variables
- TTY tests may be flaky on some systems due to terminal emulation differences
  - These tests require proper TTY allocation and may fail in some CI environments
  - Use `SKIP_TTY_TESTS=1` environment variable to skip them if needed

## Test Markers

Tests are organized with pytest markers:

- `@pytest.mark.unit` - Unit tests with mocked dependencies
- `@pytest.mark.integration` - Integration tests requiring a server
- `@pytest.mark.tty` - Tests requiring TTY functionality
- `@pytest.mark.checkpoint` - Tests requiring JuiceFS for checkpoint/restore

You can run specific test groups using:
```bash
# Run only TTY tests
pytest -m tty tests/

# Run all tests except checkpoint tests
pytest -m "not checkpoint" tests/

# Run only unit tests
pytest -m unit tests/
```