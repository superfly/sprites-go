#!/bin/sh
# Wrapper script to run the correct test_trap binary based on architecture

ARCH=$(uname -m)
SCRIPT_DIR=$(dirname "$0")

if [ "$ARCH" = "x86_64" ]; then
    exec "$SCRIPT_DIR/test_trap_linux"
elif [ "$ARCH" = "aarch64" ]; then
    exec "$SCRIPT_DIR/test_trap_linux_arm64"
else
    # Fallback to the native binary
    exec "$SCRIPT_DIR/test_trap"
fi
