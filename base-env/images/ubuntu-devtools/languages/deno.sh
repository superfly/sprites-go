#!/bin/bash
set -e

echo "=========================================="
echo "Installing Deno (canonical approach)..."
echo "=========================================="

# Configuration with argument support
BASE_DIR="${1:-/opt}"  # Default to /opt, can be overridden with first argument
LANG_BASE_DIR="$BASE_DIR/languages"
BIN_DIR="$BASE_DIR/bin"
ETC_DIR="$BASE_DIR/etc/profile.d"

# Deno specific configuration
DENO_VERSION="${DENO_VERSION:-latest}"
DENO_BASE_DIR="$LANG_BASE_DIR/deno"

echo "Installing Deno..."
echo "Base directory: $BASE_DIR"
echo "Default version: $DENO_VERSION"

# Create directories with proper permissions
echo "Creating directories..."
mkdir -p "$DENO_BASE_DIR" "$BIN_DIR" "$ETC_DIR"
chown -R $(id -u):$(id -g) "$LANG_BASE_DIR/deno" "$BIN_DIR"

# Install Deno using official install script
echo "Downloading and installing Deno..."
export DENO_INSTALL="$DENO_BASE_DIR"
curl -fsSL https://deno.land/install.sh | sh

# Create symlinks in BIN_DIR
echo "Creating symlinks in $BIN_DIR..."
for binary in "$DENO_INSTALL/bin"/*; do
    if [ -f "$binary" ] && [ -x "$binary" ]; then
        binary_name=$(basename "$binary")
        ln -sf "$binary" "$BIN_DIR/$binary_name"
        echo "  Linked: $binary_name"
    fi
done


# Verify installation
echo ""
echo "Verifying Deno installation..."
"$BIN_DIR/deno" --version

# Test Deno
echo ""
echo "Testing Deno..."
"$BIN_DIR/deno" eval 'console.log("Hello from Deno!")'

# Create profile script
echo ""
echo "Creating Deno environment configuration..."
tee $ETC_DIR/deno.sh > /dev/null << EOF
# Deno configuration
export DENO_INSTALL="$DENO_BASE_DIR"
export DENO_DIR="$LANG_BASE_DIR/deno/.cache"
export DENO_NPM_DIR="$LANG_BASE_DIR/deno/.npm"
# PATH should already include $BIN_DIR from elsewhere
EOF

# Create documentation
echo ""
echo "Creating Deno documentation..."
cat > "$LANG_BASE_DIR/deno/llm.txt" << 'EOF'
Deno Installation
=================

Deno is a secure runtime for JavaScript and TypeScript.

Installation Location:
- Deno: LANG_BASE_DIR/deno
- Binaries: BIN_DIR (symlinked)
- Cache: LANG_BASE_DIR/deno/.cache
- NPM cache: LANG_BASE_DIR/deno/.npm

Using Deno:
-----------
Deno is immediately available:
  deno --version
  deno run script.ts         # Run TypeScript/JavaScript
  deno repl                  # Interactive REPL
  deno lint                  # Lint code
  deno fmt                   # Format code
  deno test                  # Run tests

Running Code:
-------------
Basic execution:
  deno run script.ts
  deno run https://deno.land/std/examples/welcome.ts

With permissions:
  deno run --allow-net server.ts
  deno run --allow-read --allow-write file.ts
  deno run -A script.ts      # Allow all permissions

Dependencies:
-------------
Import from URLs:
  import { serve } from "https://deno.land/std@0.213.0/http/server.ts"

Import from npm:
  import express from "npm:express@4"

Lock dependencies:
  deno cache --lock=lock.json --lock-write deps.ts

Development Tools:
------------------
  deno init                  # Initialize new project
  deno lint                  # Lint TypeScript/JavaScript
  deno fmt                   # Format code
  deno test                  # Run tests
  deno bench                 # Run benchmarks
  deno doc mod.ts            # Generate documentation
  deno compile script.ts     # Create executable

Task Runner:
------------
In deno.json:
  {
    "tasks": {
      "dev": "deno run --watch main.ts",
      "test": "deno test --parallel"
    }
  }

Run tasks:
  deno task dev
  deno task test

Common Commands:
----------------
deno --version             # Check version
deno run script.ts         # Run script
deno repl                  # Start REPL
deno lint                  # Lint code
deno fmt                   # Format code
deno test                  # Run tests
deno compile script.ts     # Create executable
deno upgrade               # Update Deno
deno info                  # Show dependencies

Environment Variables:
----------------------
DENO_INSTALL               # Deno installation directory
DENO_DIR                   # Cache directory
DENO_NPM_DIR               # NPM packages cache
NO_COLOR                   # Disable colored output
DENO_CERT                  # Custom CA certificate

Permissions:
------------
--allow-env                # Environment access
--allow-hrtime             # High-resolution time
--allow-net                # Network access
--allow-ffi                # Foreign function interface
--allow-read               # File system read
--allow-run                # Subprocess execution
--allow-write              # File system write
--allow-all (-A)           # All permissions

Notes:
------
- TypeScript support built-in (no config needed)
- Secure by default (explicit permissions required)
- Single executable with no dependencies
- Standard library available at https://deno.land/std
- Compatible with npm packages via "npm:" specifier
- Uses URL imports (can be cached/vendored)
- Includes built-in formatter, linter, and test runner
EOF

# Replace placeholders in documentation
sed -i "s|LANG_BASE_DIR|$LANG_BASE_DIR|g" "$LANG_BASE_DIR/deno/llm.txt"
sed -i "s|BIN_DIR|$BIN_DIR|g" "$LANG_BASE_DIR/deno/llm.txt"

echo ""
echo "✅ Deno installed successfully!"
echo "   - Installation directory: $DENO_BASE_DIR"
echo "   - Binaries available in: $BIN_DIR"
echo "   - Version: $("$BIN_DIR/deno" --version | head -1)"
echo "   - Documentation: $LANG_BASE_DIR/deno/llm.txt"
echo ""
echo "Managing Deno:"
echo "   deno upgrade              - Upgrade to latest version"
echo "   deno upgrade --version X.Y.Z - Install specific version"