#!/bin/bash
set -e

# conforms to llm.txt and matches node layout

echo "=========================================="
echo "Installing npm-based agents..."
echo "=========================================="

# Configuration with argument support
BASE_DIR="${1:-/opt}"  # Default to /opt, can be overridden with first argument
LANG_BASE_DIR="$BASE_DIR/languages"
BIN_DIR="$BASE_DIR/bin"

# This script should run after nodejs.sh, so Node/npm should already be available
if [ ! -f "$BIN_DIR/npm" ]; then
    echo "Error: npm not found in $BIN_DIR. Make sure Node.js is installed first."
    exit 1
fi

# Get the current Node.js version path
NODE_VERSION=$($BIN_DIR/node --version | sed 's/v//')
NODE_BIN_PATH="$LANG_BASE_DIR/node/nvm/versions/node/v${NODE_VERSION}/bin"

echo "Installing agents for Node.js version: $NODE_VERSION"
echo "Node bin path: $NODE_BIN_PATH"

# Install the npm-based agents
echo "Installing @anthropic-ai/claude-code..."
$BIN_DIR/npm install -g @anthropic-ai/claude-code

echo "Installing @google/gemini-cli..."
$BIN_DIR/npm install -g @google/gemini-cli

# Check what command names were actually installed
echo ""
echo "Checking installed commands..."
echo "Looking in: $NODE_BIN_PATH"

# List all executables in the Node bin directory (for debugging)
echo "Available commands:"
ls -1 "$NODE_BIN_PATH" 2>/dev/null | sort | sed 's/^/  /'

# Look for installed executables
CLAUDE_CMD=""
GEMINI_CMD=""

# Check for claude-related commands
for cmd in claude claude-code claude-ai; do
    if [ -f "$NODE_BIN_PATH/$cmd" ]; then
        CLAUDE_CMD="$cmd"
        echo "  Found Claude command: $cmd"
        break
    fi
done

# Check for gemini-related commands  
for cmd in gemini gemini-cli gcloud-gemini; do
    if [ -f "$NODE_BIN_PATH/$cmd" ]; then
        GEMINI_CMD="$cmd"
        echo "  Found Gemini command: $cmd"
        break
    fi
done

# Create nvm-enabled shims for agents (no shell init required)
echo ""
echo "Creating nvm-enabled agent shims..."

create_nvm_shim() {
  local shim_name="$1"
  local extra_inserts=""
  if [ "$shim_name" = "gemini" ]; then
    # Ensure Gemini system instructions are enabled by default
    extra_inserts='\nexport GEMINI_SYSTEM_MD="${GEMINI_SYSTEM_MD:-true}"\n'
  fi
  cat > "$BIN_DIR/$shim_name" << 'WRAP_EOF'
#!/bin/bash
set -e

BIN_DIR="REPLACE_BIN_DIR"
DEFAULT_NVM_DIR="REPLACE_NVM_DIR"

# Only set NVM_DIR if not already set
export NVM_DIR="${NVM_DIR:-$DEFAULT_NVM_DIR}"
[ -s "$NVM_DIR/nvm.sh" ] && . "$NVM_DIR/nvm.sh"

# Activate default (if available) quietly
nvm use default >/dev/null 2>&1 || true

# Resolve active Node bin dir
NODE_BIN="$(nvm which default 2>/dev/null || nvm which current 2>/dev/null || command -v node)"
NODE_BIN_DIR="$(dirname "$NODE_BIN")"

# Prepend NODE_BIN_DIR to PATH only if not already present
case ":$PATH:" in
  *":$NODE_BIN_DIR:") ;;
  *) export PATH="$NODE_BIN_DIR:$PATH" ;;
esac

cmd_name="$(basename "$0")"
exec "$NODE_BIN_DIR/$cmd_name" "$@"
WRAP_EOF
  sed -i "s|REPLACE_BIN_DIR|$BIN_DIR|g" "$BIN_DIR/$shim_name"
  sed -i "s|REPLACE_NVM_DIR|$LANG_BASE_DIR/node/nvm|g" "$BIN_DIR/$shim_name"
  # Insert any extra exports right after 'set -e'
  if [ -n "$extra_inserts" ]; then
    sed -i "0,/^set -e$/s//set -e$extra_inserts/" "$BIN_DIR/$shim_name"
  fi
  chmod +x "$BIN_DIR/$shim_name"
  echo "  Created shim: $shim_name"
}

# Create only if commands were detected in the Node bin
[ -n "$CLAUDE_CMD" ] && create_nvm_shim "claude" || echo "  Warning: Could not find Claude command to wrap"
[ -n "$GEMINI_CMD" ] && create_nvm_shim "gemini" || echo "  Warning: Could not find Gemini command to wrap"

# Verify installation
echo ""
echo "Verifying agent installations..."
if [ -n "$CLAUDE_CMD" ]; then
    echo "✓ Claude is installed as: $CLAUDE_CMD"
else
    echo "✗ Claude installation may have failed"
fi

if [ -n "$GEMINI_CMD" ]; then
    echo "✓ Gemini is installed as: $GEMINI_CMD"
else
    echo "✗ Gemini installation may have failed"
fi

echo ""
echo "✅ npm-based agents installation completed!"
echo "   - claude command available"
echo "   - gemini command available"
echo "   - Wrappers created in: $BIN_DIR"
