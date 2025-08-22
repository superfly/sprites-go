# Sprite Integration Tests

This directory contains comprehensive integration tests for the Sprite environment, with a focus on the `/exec` endpoint and WebSocket-based command execution.

## Test Structure

### Docker-Based Integration Tests
All tests run in controlled Docker environments for consistency and reliability:

- `docker_integration_test.go` - Full-stack testing with real server
- `websocket_protocol_test.go` - WebSocket protocol compliance  
- `exec_edge_cases_test.go` - Error handling and edge cases
- `performance_test.go` - Load and performance testing
- `exec_large_output_test.go` - Large data handling
- `exec_race_condition_test.go` - Race condition detection
- `tty_test.go` - TTY functionality

## Prerequisites

1. Docker installed and running
2. Go 1.21 or later
3. No external dependencies required

## Running the Tests

```bash
# Run all tests
make test-all

# Run specific test categories
make test-websocket-protocol
make test-edge-cases
make test-performance
make test-large-output
make test-race-condition
make test-tty

# Run with specific Docker image
DOCKER_IMAGE=ubuntu:22.04 make test-all
```

## Test Categories

### 1. WebSocket Protocol Tests
- Message ordering verification
- Stream ID handling (stdout, stderr, stdin, exit)
- Connection lifecycle management
- Protocol compliance with different clients

### 2. Command Execution Tests
- Basic command execution
- Complex command chains
- Environment variable handling
- Working directory management
- Exit code propagation

### 3. TTY Mode Tests
- PTY setup and teardown
- Terminal size handling
- Raw mode functionality
- Color and control sequence preservation

### 4. Error Handling Tests
- Invalid commands
- Network disconnections
- Server restarts
- Resource exhaustion
- Authentication failures

### 5. Performance Tests
- Concurrent connections
- Large data throughput
- Memory usage under load
- Connection stability

### 6. Integration Tests
- Port monitoring functionality
- Transcript collection
- Wrapper command execution
- Checkpoint integration

## Debugging

If tests fail:
1. Check Docker logs: `docker logs <container-id>`
2. Inspect test artifacts in `test-artifacts/`
3. Run tests with verbose output: `make test-all VERBOSE=1`
4. Check server logs in the container

## Test Artifacts

Test artifacts are stored in `test-artifacts/`:
- Server logs
- WebSocket traffic captures
- Performance metrics
- Error reports

## Cleanup

Docker tests automatically clean up containers and images. If manual cleanup is needed:
```bash
docker stop $(docker ps -q --filter ancestor=sprite-test)
docker rm $(docker ps -aq --filter ancestor=sprite-test)
docker rmi sprite-test
``` 