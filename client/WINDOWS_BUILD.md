# Windows Build Instructions

The Sprite client now supports Windows builds with some platform-specific modifications.

## Building for Windows

To build the Windows client, use the `clientonly` build tag:

```bash
GOOS=windows GOARCH=amd64 go build -tags clientonly -o sprite.exe
```

Or use the Makefile:

```bash
make build-all  # Builds for all platforms including Windows
```

## Platform-Specific Changes

### 1. Terminal Resize Handling
- **Unix/Linux/macOS**: Uses `SIGWINCH` signal for terminal resize detection
- **Windows**: Terminal resize is handled automatically by Windows Terminal/ConPTY

The code uses build tags to provide platform-specific implementations:
- `client/commands/exec_unix.go` - Unix-specific resize handling
- `client/commands/exec_windows.go` - Windows-specific (no-op) implementation

### 2. Build Tags
The `clientonly` build tag excludes server-only functionality from the `pkg/terminal` package:
- `session.go` - Excluded (depends on container package)
- `websocket.go` - Excluded (server-side WebSocket handler)

This prevents compilation of Unix-specific dependencies that aren't needed for the client.

### 3. Shared Types
Common types used by both client and server code are defined in:
- `pkg/terminal/stream_types.go` - StreamID and ControlMessage types

## Requirements

- Go 1.19 or later
- Windows 10 or later (for optimal terminal support)
- Windows Terminal recommended for best experience

## Known Limitations

- Some terminal features may behave differently on Windows
- Browser opening uses Windows-specific commands (`cmd /c start`)

## Testing

The Windows build has been tested to compile successfully. Runtime testing on actual Windows systems is recommended to ensure full functionality. 