#!/bin/sh
set -euo pipefail

# Ensure Go is on PATH for non-login shells
export PATH="/usr/local/go/bin:$PATH"

# JuiceFS local-mode mount within the container (requires --privileged or /dev/fuse)
BASE=${JUICEFS_BASE:-/juicefs-base}
MNT=${JUICEFS_MNT:-/juicefs-mnt}
META="$BASE/metadata.db"
BUCKET="$BASE/local"

mkdir -p "$BUCKET" "$MNT"

# Format if not already formatted (ignore error if already formatted)
juicefs format --storage file --bucket "$BUCKET" --trash-days 7 "sqlite3://$META" spritefs >/dev/null 2>&1 || true

# Mount JuiceFS
JFS_SUPERVISOR=1 juicefs mount --no-usage-report -o writeback_cache --writeback --upload-delay=1m --no-syslog "sqlite3://$META" "$MNT" &
mount_pid=$!

# Give it a moment to be ready and create tmp inside mount
sleep 2
mkdir -p "$MNT/tmp"
export TMPDIR="$MNT/tmp"
export GOTMPDIR="$TMPDIR"

# Default command when none provided: run the repo's test script
if [ "$#" -eq 0 ]; then
  set -- ./scripts/run-tests.sh
fi

# Run the requested command, capture exit code
set +e
"$@"
ec=$?

# Cleanup: try to unmount and stop mount process
umount "$MNT" 2>/dev/null || umount --lazy "$MNT" 2>/dev/null || true
if kill -0 "$mount_pid" 2>/dev/null; then kill "$mount_pid" 2>/dev/null || true; fi

exit $ec


