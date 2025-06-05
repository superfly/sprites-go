#!/bin/bash
echo "fs: starting juicefs checkpoint..."
sleep 0.2
echo "fs: flushing pending writes..."
sleep 0.3
echo "fs: writes flushed"
echo "fs: syncing metadata..."
sleep 0.2
echo "fs: metadata synced"
echo "fs: checkpoint complete"
exit 0 