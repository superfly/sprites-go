#!/bin/sh
echo "Running ignore_signals.sh"
echo "Setting up signal traps..."
trap '' TERM INT
echo "Entering infinite loop (ignoring signals)..."
while true; do
    sleep 1
done 