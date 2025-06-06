#!/bin/bash
echo "supervised process started"
trap 'echo "supervised-process.sh: received signal SIGTERM"' SIGTERM
trap 'echo "supervised-process.sh: received signal SIGINT"' SIGINT
trap 'echo "supervised-process.sh: received signal SIGKILL"' SIGKILL
while true; do sleep 1; done 