#!/bin/bash

echo "FS: Running start.sh"

_term() {
  echo "FS: Received SIGTERM. Unmounting JuiceFS..."
  # Simulate JuiceFS unmount command
  echo "FS: JuiceFS unmounted."
  exit 0
}

_int() {
  echo "FS: Received SIGINT. Unmounting JuiceFS..."
  # Simulate JuiceFS unmount command
  echo "FS: JuiceFS unmounted."
  exit 0
}

trap _term SIGTERM
trap _int SIGINT

echo "FS: Starting JuiceFS mount..."
# Simulate JuiceFS mount command delay and output
sleep 0.5 
echo "FS: (Simulated) exec juicefs mount ..."
echo "FS: (Simulated) JuiceFS Metasyncer: [INFO] Meta sync is enabled, interval: 10s"
echo "FS: (Simulated) JuiceFS mount point: /mnt/jfs"
echo "FS: (Simulated) JuiceFS FUSE module version: x.y.z"
echo "FS: (Simulated) JuiceFS status: OK"
echo "FS: JuiceFS mounted and running. Monitoring file system operations."
echo "FS: Started" # Retain original "Started" message for consistency

# Keep the script running
while true; do
  # In a real script, the JuiceFS mount process would be running here.
  # For simulation, we just sleep.
  sleep 1 &
  wait $! # Wait for sleep to ensure signal interruption works
done