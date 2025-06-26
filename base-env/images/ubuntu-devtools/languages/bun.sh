#!/bin/bash
set -e
source /opt/asdf/asdf.sh

echo "=========================================="
echo "Installing and testing Bun..."
echo "=========================================="

echo "Adding Bun plugin..."
asdf plugin-add bun https://github.com/cometkim/asdf-bun.git
echo "Installing Bun latest..."
asdf install bun latest
echo "Setting Bun global..."
asdf global bun latest
echo "Testing Bun..."
echo 'console.log("hello");' > /tmp/hello.js
bun run /tmp/hello.js
rm /tmp/hello.js

echo "✅ Bun installed and tested successfully!" 