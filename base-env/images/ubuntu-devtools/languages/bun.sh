#!/bin/bash
set -e

echo "=========================================="
echo "Installing Bun (canonical approach)..."
echo "=========================================="

# Configuration with argument support
BASE_DIR="${1:-/opt}"  # Default to /opt, can be overridden with first argument
LANG_BASE_DIR="$BASE_DIR/languages"
BIN_DIR="$BASE_DIR/bin"
ETC_DIR="$BASE_DIR/etc/profile.d"

# Bun specific configuration
BUN_VERSION="${BUN_VERSION:-latest}"
BUN_BASE_DIR="$LANG_BASE_DIR/bun"

echo "Installing Bun..."
echo "Base directory: $BASE_DIR"
echo "Default version: $BUN_VERSION"

# Create directories with proper permissions
echo "Creating directories..."
mkdir -p "$BUN_BASE_DIR" "$BIN_DIR" "$ETC_DIR"
chown -R $(id -u):$(id -g) "$LANG_BASE_DIR/bun" "$BIN_DIR"

# Install Bun using official install script
echo "Downloading and installing Bun..."
export BUN_INSTALL="$BUN_BASE_DIR"
curl -fsSL https://bun.sh/install | bash

# Create symlinks in BIN_DIR
echo "Creating symlinks in $BIN_DIR..."
for binary in "$BUN_INSTALL/bin"/*; do
    if [ -f "$binary" ] && [ -x "$binary" ]; then
        binary_name=$(basename "$binary")
        ln -sf "$binary" "$BIN_DIR/$binary_name"
        echo "  Linked: $binary_name"
    fi
done


# Verify installation
echo ""
echo "Verifying Bun installation..."
"$BIN_DIR/bun" --version

# Test Bun
echo ""
echo "Testing Bun..."
echo 'console.log("Hello from Bun!");' > /tmp/hello.js
"$BIN_DIR/bun" run /tmp/hello.js
rm /tmp/hello.js

# Create profile script
echo ""
echo "Creating Bun environment configuration..."
tee $ETC_DIR/bun.sh > /dev/null << EOF
# Bun configuration
export BUN_INSTALL="$BUN_BASE_DIR"
export BUN_CACHE_DIR="$LANG_BASE_DIR/bun/.bun-cache"
export BUN_GLOBAL_DIR="$LANG_BASE_DIR/bun/.bun-global"
# PATH should already include $BIN_DIR from elsewhere
EOF

# Create documentation
echo ""
echo "Creating Bun documentation..."
cat > "$LANG_BASE_DIR/bun/llm.txt" << 'EOF'
Bun Installation
================

Bun is an all-in-one JavaScript runtime & toolkit.

Installation Location:
- Bun: LANG_BASE_DIR/bun
- Binaries: BIN_DIR (symlinked)
- Cache: LANG_BASE_DIR/bun/.bun-cache
- Global packages: LANG_BASE_DIR/bun/.bun-global

Using Bun:
----------
Bun is immediately available:
  bun --version
  bun init                   # Initialize new project
  bun run script.js          # Run JavaScript/TypeScript
  bun test                   # Run tests
  bun build ./index.ts       # Bundle for production

Package Management:
-------------------
Bun is a drop-in replacement for npm/yarn:
  bun install                # Install dependencies
  bun add react              # Add dependency
  bun add -d @types/react    # Add dev dependency
  bun remove react           # Remove dependency
  bun update                 # Update dependencies

Global Packages:
----------------
  bun install -g <package>   # Install globally
  bunx <package>             # Run without installing

Running Scripts:
----------------
  bun run dev                # Run package.json script
  bun run --hot server.ts    # Hot reload
  bun run --watch test.ts    # Watch mode

Bun-specific Features:
----------------------
  bun create react-app       # Create from template
  bun build ./index.tsx      # Bundle TypeScript/JSX
  bun test                   # Built-in test runner
  bunx cowsay "Hello"        # npx alternative

Common Commands:
----------------
bun --version              # Check version
bun init                   # Create package.json
bun install                # Install dependencies
bun add <package>          # Add dependency
bun run <script>           # Run script
bun test                   # Run tests
bun build <file>           # Bundle for production
bun upgrade                # Update Bun itself

Environment Variables:
----------------------
BUN_INSTALL                # Bun installation directory
BUN_CACHE_DIR              # Package cache location
BUN_GLOBAL_DIR             # Global packages location
BUN_DISABLE_UPGRADE_CHECK  # Disable auto-update check

Notes:
------
- Bun auto-updates by default (disable with BUN_DISABLE_UPGRADE_CHECK=1)
- Compatible with most npm packages
- Built-in TypeScript and JSX support
- Significantly faster than Node.js for many operations
- Includes built-in bundler, test runner, and package manager
- Uses binary lockfile (bun.lockb) for faster installs
EOF

# Replace placeholders in documentation
sed -i "s|LANG_BASE_DIR|$LANG_BASE_DIR|g" "$LANG_BASE_DIR/bun/llm.txt"
sed -i "s|BIN_DIR|$BIN_DIR|g" "$LANG_BASE_DIR/bun/llm.txt"

echo ""
echo "✅ Bun installed successfully!"
echo "   - Installation directory: $BUN_BASE_DIR"
echo "   - Binaries available in: $BIN_DIR"
echo "   - Version: $("$BIN_DIR/bun" --version)"
echo "   - Documentation: $LANG_BASE_DIR/bun/llm.txt"
echo ""
echo "Note: Bun auto-updates by default. To disable:"
echo "   export BUN_DISABLE_UPGRADE_CHECK=1"