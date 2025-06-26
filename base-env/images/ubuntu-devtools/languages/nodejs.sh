#!/bin/bash
set -e
source /opt/asdf/asdf.sh

echo "=========================================="
echo "Installing and testing Node.js..."
echo "=========================================="

echo "Adding Node.js plugin..."
asdf plugin-add nodejs https://github.com/asdf-vm/asdf-nodejs.git
echo "Installing Node.js latest..."
asdf install nodejs latest
echo "Setting Node.js global..."
asdf global nodejs latest
echo "Testing Node.js..."
node -e 'console.log("hello")'

echo "✅ Node.js installed and tested successfully!" 