# sprite-run

A command line tool that wraps program execution to run inside sprite environments, making programs appear to run locally (similar to running under tmux).

## Overview

`sprite-run` uses the urfave/cli library to provide a clean command-line interface for running programs inside sprites. It leverages the existing sprite client library to handle WebSocket connections, TTY management, and environment variables.

## Installation

```bash
cd /app/cmd/sprite-run
go build -o sprite-run
```

## Usage

### Basic Usage

```bash
# Run nano text editor in a sprite
sprite-run --org myorg --sprite mysprite nano

# Run nano with a specific file
sprite-run --org myorg --sprite mysprite nano myfile.txt

# Run with custom working directory
sprite-run --org myorg --sprite mysprite --dir /app nano config.json

# Run with environment variables
sprite-run --org myorg --sprite mysprite --env EDITOR=nano nano
```

### Environment Variables

You can set environment variables to avoid specifying flags repeatedly:

```bash
export SPRITE_ORG=myorg
export SPRITE_NAME=mysprite

# Now you can run commands without specifying --org and --sprite
sprite-run nano
```

Alternatively, you can use direct sprite connections:

```bash
export SPRITE_URL=ws://localhost:8080
export SPRITE_TOKEN=your-token

sprite-run nano
```

### Global Options

- `--org, -o`: Specify organization (can be set with `SPRITE_ORG`)
- `--sprite, -s`: Specify sprite name (can be set with `SPRITE_NAME`)
- `--dir, -d`: Working directory for the command
- `--env, -e`: Environment variables (KEY=value, can be repeated)
- `--tty, -t`: Allocate a pseudo-TTY (automatically enabled for interactive programs)
- `--help, -h`: Show help
- `--version, -v`: Print version

## Supported Programs

Currently supported programs:

- **nano**: Text editor with full TTY support

The tool is designed to be easily extensible to support additional programs.

## How It Works

1. `sprite-run` uses the urfave/cli library to parse command line arguments
2. It wraps the existing sprite client library's `ExecCommand` function
3. The sprite client handles WebSocket connections to the sprite environment
4. TTY mode is automatically enabled for interactive programs like nano
5. The program appears to run locally, with proper terminal handling

## Architecture

- **main.go**: CLI application using urfave/cli
- **SpriteRunner**: Wrapper around the sprite client library
- Uses existing sprite client APIs for command execution
- Leverages WebSocket connections for real-time communication

## Examples

### Running nano

```bash
# Simple nano execution
sprite-run --org myorg --sprite mysprite nano

# Edit a specific file
sprite-run --org myorg --sprite mysprite nano /path/to/file.txt

# Run with custom settings
sprite-run --org myorg --sprite mysprite --dir /app --env TERM=xterm-256color nano
```

### Error Handling

The tool provides clear error messages:

```bash
# No sprite configuration
$ sprite-run nano
Error: No sprite configuration found.
Please specify --org and --sprite, or set SPRITE_ORG and SPRITE_NAME environment variables.
You can also set SPRITE_URL and SPRITE_TOKEN for direct connections.
```

## Development

To add support for new programs:

1. Add a new command to the `Commands` slice in `main.go`
2. Configure appropriate TTY settings for the program
3. Set up any program-specific environment variables or flags

## Dependencies

- [urfave/cli/v2](https://github.com/urfave/cli): Command line interface library
- sprite-env/client: Existing sprite client library for command execution
- sprite-env/lib: Shared library components
- superfly/sprite-env/pkg/terminal: Terminal handling components

## License

Same as the parent sprite-env project.
