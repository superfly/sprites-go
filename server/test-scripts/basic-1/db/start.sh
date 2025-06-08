#!/bin/bash

_term() {
  echo "db-start.sh: received SIGTERM"
  exit 0
}
_int() {
  echo "db-start.sh: received SIGINT"
  exit 0
}
trap _term SIGTERM
trap _int SIGINT

echo "db: starting litestream replication..."
sleep 0.3
echo "db: litestream replication started"
echo "db: replication status: active"
echo "db: replication lag: 0s"
echo "db: replication health: healthy"

while true; do
    sleep 1
done 