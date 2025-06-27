# Handlers Package

This package contains all HTTP handlers for the Sprite Environment API server.

## Structure

The handlers are organized into logical files:

- **handlers.go** - Core `Handlers` struct and constructor
- **interfaces.go** - `SystemManager` interface definition
- **types.go** - Shared type definitions

### Handler Files

- **exec.go** - WebSocket exec endpoint for running commands
- **admin.go** - Admin operations (e.g., reset-state)
- **checkpoints.go** - Checkpoint management (create, list, get, restore)
- **debug.go** - Debug endpoints for testing
- **proxy.go** - HTTP proxy handler

### Testing

- **handlers_test.go** - Tests for core handlers
- **debug_test.go** - Tests for debug handlers

## Adding New Handlers

When adding a new handler:
1. Create a new file for logically grouped handlers (e.g., `metrics.go`)
2. Define handler methods on the `*Handlers` receiver
3. Access shared resources via the `Handlers` struct fields (logger, system, config)
4. Add corresponding tests in a `*_test.go` file