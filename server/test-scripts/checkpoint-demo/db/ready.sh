#!/bin/bash

# Simple ready check - just check if we see the "Started successfully" message
if grep -q "Started successfully" /dev/stdin; then
    echo "DB Component: Ready check passed"
    exit 0
else
    echo "DB Component: Not ready yet"
    exit 1
fi