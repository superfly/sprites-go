# Exec Endpoint Testing Findings

## Current Implementation Limitations

Testing with the sprite-env test scripts revealed several limitations in the current exec endpoint implementation that uses `exec.CommandContext`:

### 1. Signal Handling Issues
- When a process handles signals (e.g., traps SIGTERM), the exec endpoint doesn't properly propagate the exit code
- Processes that exit cleanly from signal handlers still return exit code -1
- Example: `crash_after_5s.sh` has SIGTERM handlers that exit with code 0, but exec returns -1

### 2. Timeout Enforcement Problems
- `exec.CommandContext` doesn't reliably kill processes that ignore signals
- Processes that trap and ignore SIGTERM may continue running past the timeout
- The context cancellation sends SIGTERM but doesn't escalate to SIGKILL

### 3. Resource Management
- No guarantee of proper cleanup for processes that ignore signals
- Potential for goroutine leaks if output pipes aren't properly closed
- No structured way to track process lifecycle

## Benefits of Using the Process Module

The Process module (already in the codebase) handles all these edge cases:

1. **Proper Signal Management**
   - Sends SIGTERM first for graceful shutdown
   - Escalates to SIGKILL after `GracefulShutdownTimeout`
   - Properly tracks signal handling and exit codes

2. **Robust Timeout Handling**
   - Uses context cancellation combined with signal escalation
   - Guarantees process termination even if signals are ignored

3. **Output Broadcasting**
   - Built-in support for multiple output consumers
   - Handles pipe closure and cleanup properly
   - No risk of blocking on closed pipes

4. **Event-Based State Tracking**
   - Clear lifecycle events: starting, started, stopping, stopped, failed
   - Easy to determine how a process ended
   - Structured error handling

5. **Resource Cleanup**
   - Implements io.Closer for proper cleanup
   - Manages all goroutines internally
   - No resource leaks

## Recommendation

Refactor the exec endpoint to use the Process module with `MaxRetries: 0`. This would:
- Fix all the signal handling edge cases
- Properly enforce timeouts
- Provide better error reporting
- Reduce code duplication
- Leverage already-tested functionality

See `api_server_exec_refactored.go` for a proposed implementation.