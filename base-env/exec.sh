#!/bin/bash
set -euo pipefail

if [[ $# -lt 2 ]]; then
  echo "Usage: $0 <container> <command> [args...]" >&2
  exit 1
fi

CONTAINER="app"
shift

CMD=(crun exec)

# Get working directory - prefer EXEC_DIR, fallback to WORKDIR from app-image.json
WORKING_DIR="${EXEC_DIR:-}"
if [ -z "$WORKING_DIR" ] && [ -f "/etc/app-image.json" ]; then
  # Extract WorkingDir from config, providing "/" as default
  WORKING_DIR=$(jq -r '.Config.WorkingDir // .config.WorkingDir // "/"' /etc/app-image.json 2>/dev/null || echo "/")
fi

# Add --cwd if we have a working directory
if [ -n "$WORKING_DIR" ]; then
  CMD+=(--cwd "$WORKING_DIR")
fi

# Add environment variables if EXEC_ENV is set
# EXEC_ENV should be a newline-separated list of KEY=value pairs
if [ -n "${EXEC_ENV:-}" ]; then
  # Read each line of EXEC_ENV and add as --env
  while IFS= read -r env_var; do
    if [ -n "$env_var" ]; then
      CMD+=(--env "$env_var")
    fi
  done <<< "$EXEC_ENV"
fi

# Handle TTY configuration
if [ -n "${CONSOLE_SOCKET:-}" ]; then
  # Use console-socket approach - crun creates the PTY and sends us the FD
  CMD+=(--tty --console-socket "$CONSOLE_SOCKET")
elif [ -t 1 ]; then
  # Legacy mode: add --tty if stdout is a TTY
  CMD+=(--tty)
fi

# Add container and remaining command
CMD+=("$CONTAINER" "$@")

# Run the command with stdin/stdout/stderr and TTY preserved
exec "${CMD[@]}"
