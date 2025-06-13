#!/bin/sh
echo "Running crash_after_5s.sh"
echo "Starting up normally..."
sleep 0.3
echo "Running normally..."
echo "Will crash in 5 seconds..."

# Set up signal handlers before sleeping
_term() {
  echo "crash_after_5s.sh: received SIGTERM before crash"
  exit 0
}
_int() {
  echo "crash_after_5s.sh: received SIGINT before crash"
  exit 0
}
trap _term SIGTERM
trap _int SIGINT

# Sleep for 5 seconds, then crash
sleep 5
echo "CRASH: Simulated failure after 5 seconds!"
exit 1 