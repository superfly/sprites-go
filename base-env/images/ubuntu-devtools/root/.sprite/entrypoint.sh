#!/bin/bash
set -e

# Set up mounts using sudo (privileged operations)
# (Uncomment when you need to do some mounts)
 # sudo /.sprite/setup-mounts.sh
# Not sprite — capture args in env and re-exec as sprite
echo PATH=$PATH
exec /.pilot/tini -- "$@"