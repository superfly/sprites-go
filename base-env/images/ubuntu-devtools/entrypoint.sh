#!/bin/bash
set -e

echo "127.0.0.1	sprite" >> /etc/hosts

# Set up mounts using sudo (privileged operations)
/.sprite/setup-mounts.sh

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
if [ $# -eq 0 ]; then
    # No command provided, start a shell as sprite
    exec su - sprite
else
    # Execute the provided command as sprite user  
    exec su - sprite -c "exec \$0 \"\$@\"" "$@"
fi 