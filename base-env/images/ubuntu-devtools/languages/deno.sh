#!/bin/bash
set -e

# conforms to llm.txt and matches node layout

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

# Create shims that set PATH to Deno bin without relying on profiles
echo "Creating shims in $BIN_DIR..."
create_deno_shim() {
  local shim_name="$1"
  cat > "$BIN_DIR/$shim_name" << 'WRAP_EOF'
#!/bin/bash
set -e

BIN_DIR="REPLACE_BIN_DIR"
DENO_INSTALL="REPLACE_DENO_INSTALL"

# Export DENO_INSTALL only if not already set
export DENO_INSTALL="${DENO_INSTALL:-$DENO_INSTALL}"

# Prepend Deno bin to PATH if not present
case ":$PATH:" in
  *":$DENO_INSTALL/bin:") ;;
  *) export PATH="$DENO_INSTALL/bin:$PATH" ;;
esac

cmd_name="$(basename "$0")"
exec "$DENO_INSTALL/bin/$cmd_name" "$@"
WRAP_EOF
  sed -i "s|REPLACE_BIN_DIR|$BIN_DIR|g" "$BIN_DIR/$shim_name"
  sed -i "s|REPLACE_DENO_INSTALL|$DENO_BASE_DIR|g" "$BIN_DIR/$shim_name"
  chmod +x "$BIN_DIR/$shim_name"
  echo "  Created shim: $shim_name"
}

create_deno_shim "deno"


# Verify installation
echo ""
echo "Verifying Deno installation..."
"$BIN_DIR/deno" --version

# Test Deno
echo ""
echo "Testing Deno..."
"$BIN_DIR/deno" eval 'console.log("Hello from Deno!")'


echo ""
echo "✅ Deno installed successfully!"
echo "   - Installation directory: $DENO_BASE_DIR"
echo "   - Binaries available in: $BIN_DIR"
echo "   - Version: $("$BIN_DIR/deno" --version | head -1)"
echo ""

# Cleanup Deno cache
echo "Cleaning Deno cache..."
rm -rf "$DENO_BASE_DIR/.cache" "$DENO_BASE_DIR/deps" "$DENO_BASE_DIR/registry" 2>/dev/null || true