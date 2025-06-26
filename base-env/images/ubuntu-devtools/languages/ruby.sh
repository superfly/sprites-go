#!/bin/bash
set -e
source /opt/asdf/asdf.sh

echo "=========================================="
echo "Installing and testing Ruby..."
echo "=========================================="

echo "Adding Ruby plugin..."
asdf plugin-add ruby https://github.com/asdf-vm/asdf-ruby.git
echo "Installing Ruby latest..."
asdf install ruby latest
echo "Setting Ruby global..."
asdf global ruby latest
echo "Testing Ruby..."
ruby -e 'puts "hello"'

echo "✅ Ruby installed and tested successfully!" 