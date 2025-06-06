#!/bin/bash
echo "fs: checking juicefs metadata..."
sleep 0.2
echo "fs: found metadata version 1.2.3"
echo "fs: unmounting existing filesystem..."
sleep 0.3
echo "fs: filesystem unmounted"
echo "fs: restoring metadata from backup..."
sleep 0.4
echo "fs: metadata restored"
echo "fs: remounting filesystem..."
sleep 0.2
echo "fs: filesystem mounted successfully"
exit 0 