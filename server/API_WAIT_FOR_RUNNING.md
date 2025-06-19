# API Wait-For-Running Feature

## Overview

The HTTP API server now automatically holds incoming requests when the system is not in a "Running" state. This ensures that API requests are not processed until the environment is fully ready. The wait time is configurable, with a default of 30 seconds.

## Implementation Details

### State Monitor Integration

The implementation uses the existing `StateMonitor` infrastructure to track system state transitions:

1. **APIStateMonitor** (`lib/api/state_monitor.go`): A custom state monitor that:
   - Tracks the current system state
   - Manages waiting requests using Go channels
   - Determines which states allow request processing

2. **Middleware** (`lib/api/server.go`): The `waitForRunningMiddleware` that:
   - Checks if the system is ready before processing requests
   - Waits up to the configured maximum time for the system to reach a ready state
   - Returns HTTP 503 Service Unavailable if the timeout is exceeded

### Configuration

The maximum wait time can be configured in two ways:

1. **Application Configuration** (`lib/application_config.go`):
   ```go
   config := lib.ApplicationConfig{
       APIMaxWaitTime: 3 * time.Second, // Custom 3-second timeout
       // ... other config
   }
   ```

2. **Programmatically**:
   ```go
   server := api.NewServer(addr, systemState, logger, config)
   server.SetMaxWaitTime(5 * time.Second)
   ```

If not specified, the default wait time is 30 seconds.

### States That Allow Request Processing

- **Running**: System is fully operational
- **Checkpointing**: Allow requests during checkpointing
- **Error/Stopped/ErrorRecovery/Stopping**: Terminal or error states (fail immediately)

### States That Hold Requests

- **Initializing**: System is initializing
- **Starting**: Components are starting up
- **Ready**: Components are ready but process is not yet healthy
- **Restoring**: System is restoring from a checkpoint

## Request Handling Behavior

1. When a request arrives and the system is not ready:
   - The request is held (not rejected)
   - The API waits for the system to transition to a ready state
   - If the system becomes ready within the configured timeout, the request is processed normally
   - If the timeout is exceeded, HTTP 503 is returned with the current state

2. When a request is cancelled by the client:
   - The wait is immediately terminated
   - Resources are cleaned up properly

## Benefits

1. **Improved Reliability**: Prevents requests from failing during system startup
2. **Better User Experience**: Clients don't need to implement retry logic for startup scenarios
3. **Transparent**: Works automatically for all API endpoints that need it
4. **Configurable**: Different endpoints can opt-in or opt-out of waiting, and timeout is adjustable

## Testing

The implementation includes comprehensive unit tests in `lib/api/server_test.go`:

- `TestWaitForRunningMiddleware`: Tests basic scenarios
- `TestWaitForRunningMiddlewareTimeout`: Tests timeout behavior
- `TestWaitForRunningMiddlewareWithCustomTimeout`: Tests with configurable timeouts (including 3s)
- `TestWaitForRunningMiddlewareEdgeCases`: Tests concurrent requests and state transitions

The tests verify:
- Correct behavior when system is already running
- Proper waiting when system becomes ready
- Timeout enforcement
- Request cancellation handling
- Multiple concurrent requests
- State transitions during wait

## Usage

No changes are required to use this feature. The API server automatically applies the wait behavior to:

- `/exec` endpoint - Waits for system to be running
- `/` (proxy) endpoint - Waits for system to be running
- `/checkpoint` and `/restore` endpoints - Do NOT wait (they may be used during startup)

## Example

When the system is starting with slow components:

```bash
# API request made immediately after system start
curl -X POST http://localhost:8090/exec \
  -H "Content-Type: application/json" \
  -H "fly-replay-src: state=api:$SPRITE_HTTP_API_TOKEN" \
  -d '{"command": ["echo", "hello"]}'

# The request will be held until the system is ready (up to configured timeout)
# Then processed normally once the system reaches "Running" state
```

### Example with Custom Timeout

To use a custom 3-second timeout:

```json
{
  "api_max_wait_time": 3000000000,  // 3 seconds in nanoseconds
  "process_command": ["./app"],
  "components": {
    // ... component configuration
  }
}
```