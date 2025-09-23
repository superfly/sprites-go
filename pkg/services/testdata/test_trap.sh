#!/bin/sh
# Test script that ignores SIGTERM to test force kill functionality
# Note: SIGKILL (9) cannot be trapped - only SIGTERM (15) can be ignored

# Trap and ignore SIGTERM
trap '' TERM

# Also ignore SIGINT and SIGHUP for good measure
trap '' INT HUP

# Make sure we're not exiting on any errors
set +e

# Keep the process running with explicit loop
while [ 1 -eq 1 ]; do
    sleep 1
done
