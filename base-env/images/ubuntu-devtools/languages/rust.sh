#!/bin/bash
set -e
source /opt/asdf/asdf.sh

echo "=========================================="
echo "Installing and testing Rust..."
echo "=========================================="

echo "Adding Rust plugin..."
asdf plugin-add rust https://github.com/code-lever/asdf-rust.git
echo "Installing Rust latest..."
asdf install rust latest
echo "Setting Rust global..."
asdf global rust latest
echo "Testing Rust..."
echo 'fn main() { println!("hello"); }' > /tmp/hello.rs
rustc /tmp/hello.rs -o /tmp/hello
/tmp/hello
rm /tmp/hello.rs /tmp/hello

echo "✅ Rust installed and tested successfully!" 