#!/bin/bash
# Entrypoint that ensures proper environment setup for sprite user

# If running as sprite user, set up the environment for version managers
if [ "$(id -un)" = "sprite" ]; then
    # Source nvm for Node.js (required for non-interactive shells)
    export NVM_DIR="/home/sprite/.nvm"
    [ -s "$NVM_DIR/nvm.sh" ] && . "$NVM_DIR/nvm.sh"
    
    # pyenv and rbenv work via shims in PATH, which we've already set in Dockerfile
    # But we should initialize them for their full functionality
    export PYENV_ROOT="/home/sprite/.pyenv"
    export RBENV_ROOT="/home/sprite/.rbenv"
    
    # Source cargo env for Rust
    [ -s "/home/sprite/.cargo/env" ] && . "/home/sprite/.cargo/env"
fi

# Execute the command
exec "$@"
