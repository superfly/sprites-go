# Handlers Package

This package contains all HTTP handlers for the Sprite Environment API server.

## Structure

The handlers are organized into logical files:

- **handlers.go** - Core `Handlers` struct and constructor
- **interfaces.go** - `SystemManager` interface definition
- **types.go** - Shared type definitions

### Handler Files

- **exec.go** - WebSocket exec endpoint for running commands
- **exec_ws_core.go** - Core exec logic reusable for WebSocket and control operations
- **exec_http.go** - HTTP POST /exec fallback endpoint
- **control.go** - WebSocket control endpoint with operation multiplexing
- **proxy.go** - HTTP proxy handler
- **proxy_ws_core.go** - Core proxy logic for WebSocket and control operations
- **checkpoints.go** - Checkpoint management (create, list, get, restore, delete)
- **handlers_policy.go** - Network policy configuration endpoint
- **admin.go** - Admin operations (e.g., reset-state)
- **debug.go** - Debug endpoints for testing

### Testing

- **handlers_test.go** - Tests for core handlers
- **debug_test.go** - Tests for debug handlers
- **control_test.go** - Tests for control endpoint
- **control_proxy_test.go** - Tests for proxy over control
- **control_sdk_test.go** - Tests for SDK control integration
- **exec_http_test.go** - Tests for HTTP POST exec
- **checkpoints_test.go** - Tests for checkpoint operations
- **services_streaming_test.go** - Tests for streaming services

## Adding New Handlers

When adding a new handler:
1. Create a new file for logically grouped handlers (e.g., `metrics.go`)
2. Define handler methods on the `*Handlers` receiver
3. Access shared resources via the `Handlers` struct fields (logger, system, config)
4. Add corresponding tests in a `*_test.go` file

## Control Operations

The control endpoint (`/control`) provides a multiplexed WebSocket connection that supports
multiple operations over a single connection. Operations are registered with a router and
can reuse core WebSocket logic from `exec_ws_core.go` and `proxy_ws_core.go`.