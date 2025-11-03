# Unified Service Manager Implementation Summary

## Overview
Successfully unified service management across the codebase by extending `pkg/services` to handle both process-based services and Go module services (DBManager, JuiceFS, etc.) with dependency-based startup/shutdown, parallel execution, and progress monitoring.

## Key Components Implemented

### 1. Core Service Manager Extensions (`pkg/services/`)

#### `types.go`
- Added `ProgressReporter` interface for services to report progress during start/stop
- Added `ManagedService` interface for Go modules (vs process-based services)
- Added `ServiceDefinition` type that wraps both process and managed services
- Added `MaxHungDuration` field for long-running operations

#### `timeout.go` (NEW)
- Implemented `progressReporter` with heartbeat tracking
- Created `startWithMonitoring()` and `stopWithMonitoring()` wrappers
- Progress monitoring logs warnings after 30s, errors after configurable timeout (default 2min)
- Services can call `progress.ReportProgress(message)` to reset hung timer
- Critical for operations like JuiceFS mount and litestream restore that can take minutes

#### `manager.go`
- Added `serviceDefs map[string]*ServiceDefinition` field
- Added `opRegisterService` and `opStopServiceTree` operations
- Implemented `RegisterService()` public API
- Implemented `StopServiceTree()` for partial shutdowns

#### `handlers.go`
- Implemented `handleRegisterService()` - registers service definitions
- Implemented `handleStopServiceTree()` - stops service and all dependents
- Updated `handleStartAll()` to support both service types
- Added parallel startup within dependency levels using goroutines
- Services at same dependency level start concurrently

### 2. System Service Wrappers (`server/system/managed_services.go` - NEW)

Created ManagedService wrappers for all system components:
- `AdminChannelService` - wraps AdminChannel
- `APIServerService` - wraps API server
- `SocketServerService` - wraps socket server
- `DBManagerService` - wraps db.Manager with progress reporting
- `JuiceFSService` - wraps juicefs.JuiceFS with progress reporting
- `OverlayService` - wraps overlay.Manager
- `ContainerService` - wraps container process lifecycle
- `ServicesManagerService` - wraps services.Manager (for user services)
- `ReaperService` - wraps zombie reaper
- `ActivityMonitorService` - wraps activity monitor

Each wrapper implements `Start()` and `Stop()` with `ProgressReporter` parameter.

### 3. System Integration (`server/system/`)

#### `system.go`
- Added `UnifiedServiceManager *services.Manager` field to System struct
- Separated from `ServicesManager` (which manages user/process services)

#### `services.go`
- Added `initializeUnifiedServiceManager()` - creates the manager
- Added `registerSystemServices()` - registers all system services with dependencies:
  - Level 0: reaper, activity_monitor, admin_channel, api_server, socket_server (parallel)
  - Level 1: db_manager
  - Level 2: juicefs (depends on db_manager)
  - Level 3: overlay (depends on juicefs)
  - Level 4: container (depends on overlay)
  - Level 5: services_manager (depends on container)

#### `system_boot.go`
- **SIMPLIFIED** from ~250 lines to ~100 lines
- Replaced manual orchestration with `registerSystemServices()` + `StartAll()`
- Kept post-boot hooks (cgroup moves, hostname, policy setup)
- All service coordination now handled by unified manager

#### `system_shutdown.go`
- **SIMPLIFIED** shutdown from ~180 lines to ~30 lines
- Replaced manual phase-by-phase shutdown with `Shutdown()`
- Manager handles reverse dependency order automatically
- Updated `ShutdownContainer()` to use `StopServiceTree("container")`

## Dependency Graph

```
Utilities (Level 0 - parallel):
├─ reaper
├─ activity_monitor
├─ admin_channel
├─ api_server
└─ socket_server

Storage Stack (Levels 1-5 - sequential):
db_manager (L1)
  ↓
juicefs (L2)
  ↓
overlay (L3)
  ↓
container (L4)
  ↓
services_manager (L5)
  └─ user_services (managed separately)
```

## Benefits

### 1. Reliable Startup
- Services start in parallel when possible (same dependency level)
- Dependencies enforced automatically
- Progress monitoring prevents false hung detection
- DBManager and JuiceFS can report progress during long operations

### 2. Reliable Shutdown
- Automatic reverse dependency order
- Partial shutdowns via `StopServiceTree()` (e.g., stop container + dependents)
- Data integrity preserved (critical services use background context)

### 3. Restart Support
- Service manager supports repeated start/stop cycles
- Each service can be restarted independently
- Proper cleanup and state management

### 4. Progress Reporting
- Long operations (litestream restore, juicefs mount) report progress
- Hung detection only triggers if no progress for configured duration
- Default: 2 minutes without progress = hung
- Configurable per-service via `MaxHungDuration`

## Usage Example

```go
// Boot - simplified
func (s *System) Boot(ctx context.Context) error {
    // Register all services
    if err := s.registerSystemServices(); err != nil {
        return err
    }
    
    // Start all in parallel by dependency level
    if err := s.UnifiedServiceManager.StartAll(); err != nil {
        return err
    }
    
    // Done!
    return nil
}

// Shutdown - simplified
func (s *System) Shutdown(ctx context.Context) error {
    // Stop all in reverse dependency order
    return s.UnifiedServiceManager.Shutdown()
}

// Partial shutdown
func (s *System) ShutdownContainer(ctx context.Context) error {
    // Stops container, overlay, and services_manager (anything depending on container)
    return s.UnifiedServiceManager.StopServiceTree("container")
}
```

## Progress Reporting Example

```go
func (s *JuiceFSService) Start(ctx context.Context, progress services.ProgressReporter) error {
    progress.ReportProgress("mounting JuiceFS filesystem")
    // ... mount logic ...
    
    progress.ReportProgress("verifying mount")
    // ... verification ...
    
    progress.ReportProgress("JuiceFS mounted and ready")
    return nil
}
```

## Testing Considerations

- Existing boot/shutdown tests should continue to work
- New tests needed for:
  - Parallel startup at same dependency level
  - Progress reporting and hung detection
  - StopServiceTree partial shutdowns
  - Repeated start/stop cycles
  - Service failures during startup

## Migration Notes

- Old hardcoded boot sequence removed from `system_boot.go`
- Old hardcoded shutdown removed from `system_shutdown.go`
- `BootContainer()` method preserved but simplified
- Post-boot hooks (cgroup moves, etc.) still executed after StartAll()
- Special logic (network policy, hostname) temporarily kept outside manager

## Future Improvements

1. Move network policy setup into a managed service
2. Add more granular dependency specifications
3. Consider health checks for services
4. Add metrics/telemetry for service startup times
5. Consider making some services optional based on config

