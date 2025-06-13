#!/bin/sh
echo "Running ready_fails.sh" >&2
echo "Checking component readiness..." >&2
echo "ERROR: Component failed to start properly!" >&2
echo "Ready check failed" >&2
exit 1 