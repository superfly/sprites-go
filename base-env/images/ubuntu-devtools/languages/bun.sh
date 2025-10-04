#!/bin/bash
set -e

# conforms to llm.txt and matches node layout

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

# Create manager-aware shims (no profile reliance)
echo "Creating shims in $BIN_DIR..."
create_bun_shim() {
  local shim_name="$1"
  cat > "$BIN_DIR/$shim_name" << 'WRAP_EOF'
#!/bin/bash
set -e

BIN_DIR="REPLACE_BIN_DIR"
BUN_INSTALL="REPLACE_BUN_INSTALL"

# Export BUN_INSTALL only if not already set
export BUN_INSTALL="${BUN_INSTALL:-$BUN_INSTALL}"

# Prepend Bun bin to PATH if not present
case ":$PATH:" in
  *":$BUN_INSTALL/bin:") ;;
  *) export PATH="$BUN_INSTALL/bin:$PATH" ;;
esac

cmd_name="$(basename "$0")"
exec "$BUN_INSTALL/bin/$cmd_name" "$@"
WRAP_EOF
  sed -i "s|REPLACE_BIN_DIR|$BIN_DIR|g" "$BIN_DIR/$shim_name"
  sed -i "s|REPLACE_BUN_INSTALL|$BUN_BASE_DIR|g" "$BIN_DIR/$shim_name"
  chmod +x "$BIN_DIR/$shim_name"
  echo "  Created shim: $shim_name"
}

# Core Bun entry points
create_bun_shim "bun"
create_bun_shim "bunx"


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

echo ""
echo "✅ Bun installed successfully!"
echo "   - Installation directory: $BUN_BASE_DIR"
echo "   - Binaries available in: $BIN_DIR"
echo "   - Version: $("$BIN_DIR/bun" --version)"
echo ""

# Cleanup bun cache
echo "Cleaning Bun cache..."
rm -rf "$BUN_BASE_DIR/_" "$BUN_BASE_DIR/cache" 2>/dev/null || true