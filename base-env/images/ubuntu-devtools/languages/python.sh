#!/bin/bash
set -e
source /opt/asdf/asdf.sh

echo "=========================================="
echo "Installing and testing Python..."
echo "=========================================="

echo "Adding Python plugin..."
asdf plugin-add python https://github.com/danhper/asdf-python.git
echo "Installing Python latest..."
asdf install python 3.13.3
echo "Setting Python global..."
asdf global python 3.13.3
echo "Testing Python..."
python -c 'print("hello")'

echo "✅ Python installed and tested successfully!" 