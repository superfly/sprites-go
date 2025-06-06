#!/bin/bash

echo "SUPERVISED_PROCESS: Starting"

_term() {
  echo "SUPERVISED_PROCESS: Received SIGTERM"
  exit 0
}

_int() {
  echo "SUPERVISED_PROCESS: Received SIGINT"
  exit 0
}

trap _term SIGTERM
trap _int SIGINT

# Keep the script running
while true; do
  sleep 1 &
  wait $!
done