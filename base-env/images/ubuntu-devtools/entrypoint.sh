#!/bin/bash
set -e

export PATH="/usr/local/bin:\
/usr/bin:\
/bin:\
/usr/local/sbin:\
/usr/sbin:\
/sbin:\
/home/sprite/.local/bin:\
$PATH"


echo "127.0.0.1	sprite" >> /etc/hosts
# Set up mounts using sudo (privileged operations)
/.sprite/setup-mounts.sh
# Not sprite — capture args in env and re-exec as sprite
exec gosu "$TARGET_USER" "$@"