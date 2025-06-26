#!/bin/bash
set -e
source /opt/asdf/asdf.sh

echo "=========================================="
echo "Installing and testing Go..."
echo "=========================================="

echo "Adding Go plugin..."
asdf plugin-add golang https://github.com/kennyp/asdf-golang.git
echo "Installing Go latest..."
asdf install golang latest
echo "Setting Go global..."
asdf global golang latest
echo "Testing Go..."
echo 'package main; import "fmt"; func main() { fmt.Println("hello") }' > /tmp/hello.go
go run /tmp/hello.go
rm /tmp/hello.go

echo "✅ Go installed and tested successfully!" 