#!/bin/bash
echo "supervised process started"

_term() {
  echo "supervised-process.sh: received signal SIGTERM"
  exit 0
}

_int() {
  echo "supervised-process.sh: received signal SIGINT"
  exit 0
}

trap _term SIGTERM
trap _int SIGINT

# Keep the script running
while true; do
  sleep 1 &
  wait $!
done 