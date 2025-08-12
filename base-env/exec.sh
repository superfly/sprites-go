#!/bin/bash
set -euo pipefail

if [[ $# -lt 2 ]]; then
  echo "Usage: $0 <container> <command> [args...]" >&2
  exit 1
fi

CONTAINER="app"
shift

CMD=(crun exec)

# Read app-image.json once if it exists
APP_IMAGE_CONFIG=""
if [ -f "/etc/app-image.json" ]; then
  APP_IMAGE_CONFIG=$(cat /etc/app-image.json)
fi

# Get working directory - prefer EXEC_DIR, fallback to WORKDIR from app-image.json
WORKING_DIR="${EXEC_DIR:-}"
if [ -z "$WORKING_DIR" ] && [ -n "$APP_IMAGE_CONFIG" ]; then
  # Extract WorkingDir from config, providing "/" as default
  WORKING_DIR=$(echo "$APP_IMAGE_CONFIG" | jq -r '.Config.WorkingDir // .config.WorkingDir // "/"' 2>/dev/null || echo "/")
fi

# Add --cwd if we have a working directory
if [ -n "$WORKING_DIR" ]; then
  CMD+=(--cwd "$WORKING_DIR")
fi

# Add environment variables from container config (filtered) and EXEC_ENV
if [ -n "$APP_IMAGE_CONFIG" ]; then
  # Extract environment variables from container config, filtering out sensitive ones
  # Filter APP_RUNNER_*, SPRITE_*, and FLY_* vars from JSON env
  json_env_vars=$(echo "$APP_IMAGE_CONFIG" | jq -r '.Config.Env // .config.Env // [] | map(select(startswith("APP_RUNNER_") or startswith("SPRITE_") or startswith("FLY_") | not)) | .[]' 2>/dev/null || true)
  
  # Add container config environment variables
  while IFS= read -r env_var; do
    if [ -n "$env_var" ]; then
      CMD+=(--env "$env_var")
    fi
  done <<< "$json_env_vars"
fi

# Add user-provided environment variables with EXEC_ENV_ prefix
for env_var in $(env | grep '^EXEC_ENV_' | cut -d'=' -f1); do
  if [ -n "${!env_var:-}" ]; then
    CMD+=(--env "${!env_var}")
  fi
done

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
