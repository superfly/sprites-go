#!/bin/bash

_term() {
  echo "fs-start.sh: received SIGTERM"
  exit 0
}
_int() {
  echo "fs-start.sh: received SIGINT"
  exit 0
}
trap _term SIGTERM
trap _int SIGINT

echo "fs: starting juicefs mount..."
sleep 0.2
echo "fs: connecting to metadata service..."
sleep 0.3
echo "fs: metadata service connected"
echo "fs: mounting filesystem..."
sleep 0.2
echo "fs: filesystem mounted successfully"
echo "fs: mount point: /mnt/juicefs"
echo "fs: metadata: sqlite3:///var/lib/juicefs/meta.db"
echo "fs: storage: s3://my-bucket/juicefs"

while true; do
    sleep 1
done 