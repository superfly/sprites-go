#!/bin/bash
set -e

# Set up mounts using sudo (privileged operations)
sudo /.sprite/setup-mounts.sh
# Not sprite — capture args in env and re-exec as sprite
exec /.pilot/tini -- "$@"