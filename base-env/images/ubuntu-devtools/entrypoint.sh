#!/bin/bash
set -e

# Set up mounts using sudo (privileged operations)
sudo /.sprite/setup-mounts.sh

# Set up PATH for interactive shell usage
export PATH="/usr/local/bin:\
/usr/bin:\
/bin:\
/usr/local/sbin:\
/usr/sbin:\
/sbin:\
/home/sprite/.local/bin:\
$PATH"

# Execute the original command as sprite user
exec "$@" 