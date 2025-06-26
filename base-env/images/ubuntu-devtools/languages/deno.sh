#!/bin/bash
set -e
source /opt/asdf/asdf.sh

echo "=========================================="
echo "Installing and testing Deno..."
echo "=========================================="

echo "Adding Deno plugin..."
asdf plugin-add deno https://github.com/asdf-community/asdf-deno.git
echo "Installing Deno latest..."
asdf install deno latest
echo "Setting Deno global..."
asdf global deno latest
echo "Testing Deno..."
deno eval 'console.log("hello")'

echo "✅ Deno installed and tested successfully!" 