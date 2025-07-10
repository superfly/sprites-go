# sprite-run

A command line tool that connects directly to sprite environments via WebSocket to execute programs, making them appear to run locally (similar to running under tmux).

## Overview

`sprite-run` uses the urfave/cli library to provide a clean command-line interface for running programs inside sprites. It directly connects to sprite environments via WebSocket without requiring the sprite client executable.

## Installation

```bash
cd /app/cmd/sprite-run
go build -o sprite-run
```

## Usage

### Basic Usage

```bash
# Run nano text editor in a sprite
sprite-run --url ws://localhost:8080 --token YOUR_TOKEN nano

# Run nano with a specific file
sprite-run --url ws://localhost:8080 --token YOUR_TOKEN nano myfile.txt

# Run any command
sprite-run --url ws://localhost:8080 --token YOUR_TOKEN run ls -la

# Run with custom working directory
sprite-run --url ws://localhost:8080 --token YOUR_TOKEN --dir /app nano config.json

# Run with environment variables
sprite-run --url ws://localhost:8080 --token YOUR_TOKEN --env EDITOR=nano nano
```

### Environment Variables

You can set environment variables to avoid specifying flags repeatedly:

```bash
export SPRITE_URL=ws://localhost:8080
export SPRITE_TOKEN=your-token

# Now you can run commands without specifying --url and --token
sprite-run nano
sprite-run run ls -la
```

### HTTPS/WSS Support

The tool supports both HTTP/HTTPS and WS/WSS URLs:

```bash
# WebSocket URLs
sprite-run --url ws://localhost:8080 --token TOKEN nano
sprite-run --url wss://sprite.example.com --token TOKEN nano

# HTTP URLs (automatically converted to WebSocket)
sprite-run --url http://localhost:8080 --token TOKEN nano
sprite-run --url https://sprite.example.com --token TOKEN nano
```

### Global Options

- `--url, -u`: Sprite WebSocket URL (required, can be set with `SPRITE_URL`)
- `--token, -t`: Authentication token (required, can be set with `SPRITE_TOKEN`)
- `--dir, -d`: Working directory for the command
- `--env, -e`: Environment variables (KEY=value, can be repeated)
- `--tty`: Force TTY mode (automatically detected for interactive programs)
- `--no-tty`: Disable TTY mode
- `--help, -h`: Show help
- `--version, -v`: Print version

## Commands

### nano

Run the nano text editor with full TTY support:

```bash
sprite-run nano [nano-options] [file...]
```

### run

Run any command with automatic TTY detection:

```bash
sprite-run run command [args...]
```

### Direct Command Execution

You can also run commands directly without subcommands:

```bash
sprite-run ls -la
sprite-run bash
sprite-run python script.py
```

## TTY Mode

The tool automatically detects when TTY mode should be used based on the command:

- **Interactive programs** (nano, vim, bash, htop, etc.) automatically use TTY mode
- **Non-interactive programs** (ls, cat, etc.) run without TTY by default
- Use `--tty` to force TTY mode
- Use `--no-tty` to disable TTY mode

## How It Works

1. `sprite-run` parses command line arguments using urfave/cli
2. It directly connects to the sprite environment via WebSocket
3. Commands are executed remotely with proper terminal handling
4. TTY mode provides full terminal capabilities for interactive programs
5. The program appears to run locally with seamless I/O

## Architecture

- **Direct WebSocket Connection**: No intermediate sprite client executable
- **Terminal Handling**: Full PTY support with terminal resizing
- **Auto-detection**: Smart TTY mode detection based on command type
- **Clean Interface**: Simple, intuitive command-line interface

## Examples

### Running nano

```bash
# Simple nano execution
sprite-run --url ws://localhost:8080 --token TOKEN nano

# Edit a specific file
sprite-run --url ws://localhost:8080 --token TOKEN nano /path/to/file.txt

# Run with custom settings
sprite-run --url ws://localhost:8080 --token TOKEN --dir /app --env TERM=xterm-256color nano
```

### Running various commands

```bash
# List files
sprite-run --url ws://localhost:8080 --token TOKEN ls -la

# Interactive shell
sprite-run --url ws://localhost:8080 --token TOKEN bash

# Run a script
sprite-run --url ws://localhost:8080 --token TOKEN python script.py

# System monitoring
sprite-run --url ws://localhost:8080 --token TOKEN htop
```

### Using environment variables

```bash
export SPRITE_URL=wss://sprite.example.com
export SPRITE_TOKEN=your-secure-token

# Now commands are much simpler
sprite-run nano
sprite-run run ls -la
sprite-run bash
```

## Error Handling

The tool provides clear error messages:

```bash
# Missing required flags
$ sprite-run nano
Error: Required flags "url, token" not set

# Connection issues
$ sprite-run --url ws://localhost:8080 --token TOKEN nano
Error: Failed to start command: failed to connect: dial tcp [::1]:8080: connect: connection refused
```

## Development

To add support for new programs or modify TTY detection:

1. Update the `shouldUseTTY()` function in `main.go`
2. Add new commands to the `Commands` slice if needed
3. Test with actual sprite environments

## Dependencies

- [urfave/cli/v2](https://github.com/urfave/cli): Command line interface library
- superfly/sprite-env/pkg/terminal: Direct terminal handling for WebSocket connections
- golang.org/x/term: Terminal utilities for PTY mode

## License

Same as the parent sprite-env project.
