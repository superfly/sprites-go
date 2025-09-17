#!/bin/bash
set -e

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

# Create wrapper scripts that don't require nvm to be sourced
echo ""
echo "Creating wrapper scripts..."

# Claude wrapper
if [ -n "$CLAUDE_CMD" ]; then
    cat > "$BIN_DIR/claude" << EOF
#!/bin/bash
# Wrapper for @anthropic-ai/claude-code
# Directly executes from the Node.js version it was installed with
exec "$NODE_BIN_PATH/$CLAUDE_CMD" "\$@"
EOF
    chmod +x "$BIN_DIR/claude"
    echo "  Created wrapper: claude -> $CLAUDE_CMD"
else
    echo "  Warning: Could not find Claude command to wrap"
fi

# Gemini wrapper
if [ -n "$GEMINI_CMD" ]; then
    cat > "$BIN_DIR/gemini" << EOF
#!/bin/bash
# Wrapper for @google/gemini-cli  
# Directly executes from the Node.js version it was installed with
exec "$NODE_BIN_PATH/$GEMINI_CMD" "\$@"
EOF
    chmod +x "$BIN_DIR/gemini"
    echo "  Created wrapper: gemini -> $GEMINI_CMD"
else
    echo "  Warning: Could not find Gemini command to wrap"
fi

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
