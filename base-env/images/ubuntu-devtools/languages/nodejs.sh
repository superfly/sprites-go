#!/bin/bash
set -e

# Implementation notes:
# See ./llm.txt in this directory for the filesystem layout and shim standard
# that other languages should follow (manager-first install, nvm-style shims).
# conforms to llm.txt and matches node layout

echo "=========================================="
echo "Installing Node.js (canonical nvm approach)..."
echo "=========================================="

# Configuration with argument support
BASE_DIR="${1:-/opt}"  # Default to /opt, can be overridden with first argument
LANG_BASE_DIR="$BASE_DIR/languages"
BIN_DIR="$BASE_DIR/bin"
ETC_DIR="$BASE_DIR/etc/profile.d"

# Node.js specific configuration
# Baseline pinned LTS as of 2025-10-04: 22.20.0
NODE_VERSION="${NODE_VERSION:-22.20.0}"
NVM_VERSION="${NVM_VERSION:-v0.39.4}"
NVM_DIR="$LANG_BASE_DIR/node/nvm"

echo "Installing nvm and Node.js..."
echo "Base directory: $BASE_DIR"
echo "Default version: $NODE_VERSION"

# Create directories with proper permissions
echo "Creating directories..."
mkdir -p "$NVM_DIR" "$BIN_DIR" "$ETC_DIR"
chown -R $(id -u):$(id -g) "$LANG_BASE_DIR/node" "$BIN_DIR"

# Install nvm
echo "Downloading and installing nvm ${NVM_VERSION}..."
export NVM_DIR="$NVM_DIR"
curl -o- "https://raw.githubusercontent.com/nvm-sh/nvm/${NVM_VERSION}/install.sh" | bash

# Source nvm to use it
[ -s "$NVM_DIR/nvm.sh" ] && \. "$NVM_DIR/nvm.sh"

# Remove .git directory if it exists (nvm install script may create one)
[ -d "$NVM_DIR/.git" ] && rm -rf "$NVM_DIR/.git"

# Install default Node.js version
echo "Installing Node.js ${NODE_VERSION}..."
nvm install "$NODE_VERSION"
nvm alias default "$NODE_VERSION"
nvm use default

# Install global npm packages that are commonly needed
echo "Installing common global packages..."
npm install -g npm@latest

# No global PATH modification; shims handle PATH at runtime

# Create wrapper shims in BIN_DIR for core Node.js commands
echo "Creating nvm-enabled shims in $BIN_DIR..."
for cmd in node npm npx corepack; do
    cat > "$BIN_DIR/$cmd" << 'WRAP_EOF'
#!/bin/bash
set -e

# nvm-enabled shim that ensures active Node.js is available
BIN_DIR="REPLACE_BIN_DIR"
DEFAULT_NVM_DIR="REPLACE_NVM_DIR"

# Only set NVM_DIR if not already set
export NVM_DIR="${NVM_DIR:-$DEFAULT_NVM_DIR}"
[ -s "$NVM_DIR/nvm.sh" ] && . "$NVM_DIR/nvm.sh"

# Activate default (if available) without noisy output
nvm use default >/dev/null 2>&1 || true

# Resolve the Node binary directory for the active/default toolchain
NODE_BIN="$(nvm which default 2>/dev/null || nvm which current 2>/dev/null || command -v node)"
NODE_BIN_DIR="$(dirname "$NODE_BIN")"

# Add NODE_BIN_DIR to PATH only if not already present
case ":$PATH:" in
  *":$NODE_BIN_DIR:") ;;
  *) export PATH="$NODE_BIN_DIR:$PATH" ;;
esac

cmd_name="$(basename "$0")"
exec "$NODE_BIN_DIR/$cmd_name" "$@"
WRAP_EOF
    sed -i "s|REPLACE_BIN_DIR|$BIN_DIR|g" "$BIN_DIR/$cmd"
    sed -i "s|REPLACE_NVM_DIR|$NVM_DIR|g" "$BIN_DIR/$cmd"
    chmod +x "$BIN_DIR/$cmd"
    echo "  Created shim: $cmd"
done


# Verify installation
echo ""
echo "Verifying Node.js installation..."
"$BIN_DIR/node" --version
"$BIN_DIR/npm" --version

# Show installed versions
echo ""
echo "Installed Node.js versions:"
nvm list

# Test Node.js
echo ""
echo "Testing Node.js..."
"$BIN_DIR/node" -e "console.log('Hello from Node.js ' + process.version + '!')"

# Cleanup caches to reduce image size
echo "Cleaning up Node.js caches..."
npm cache clean --force || true
rm -rf "$LANG_BASE_DIR/node/.npm-cache" "$NVM_DIR/.cache" 2>/dev/null || true

# No helper script; nvm is sourced directly by shims

# No profile script; shims ensure PATH dynamically

# Create documentation
echo ""
echo "Creating Node.js documentation..."
cat > "$LANG_BASE_DIR/node/llm.txt" << 'EOF'
Node.js Installation (via nvm)
==============================

This installation uses nvm for managing Node.js versions.

Installation Location:
- nvm: LANG_BASE_DIR/node/nvm
- Binaries: BIN_DIR (symlinked from active version)
- npm cache: LANG_BASE_DIR/node/.npm-cache

Default Version: NODE_VERSION

Using Node.js:
--------------
The default Node.js version is immediately available:
  node --version
  npm --version
  npx --version
  npm install <package>
  npm run <script>

Managing Versions:
------------------
Option 1: Use the helper script (no sourcing required):
  nvm-helper install 18.17.0  # Install a new version
  nvm-helper list             # List installed versions
  nvm-helper use 18.17.0      # Switch version & update symlinks

Option 2: Use nvm directly (requires environment setup):
  nvm install 18.17.0
  nvm use 18.17.0
  nvm alias default 18.17.0
  nvm list

Installing npm Packages:
------------------------
Local packages (in project):
  npm install express
  npm install --save-dev nodemon

Global packages (for current Node version):
  npm install -g typescript
  npm install -g @angular/cli

To install for all versions, switch versions and install:
  nvm use 20.17.0 && npm install -g <package>
  nvm use 21.6.0 && npm install -g <package>

Common Commands:
----------------
node --version              # Check Node.js version
npm --version               # Check npm version
npm init                    # Create package.json
npm install                 # Install dependencies
npm run <script>            # Run package.json script
npx <package>               # Run package without installing

Environment Variables:
----------------------
NVM_DIR                     # nvm installation directory
NODE_PATH                   # Additional module directories
NPM_CONFIG_PREFIX           # npm global installation prefix
NPM_CONFIG_CACHE            # npm cache location

Notes:
------
- nvm is a shell function, not a binary
- Each Node.js version has its own global packages
- Use .nvmrc files in projects to specify Node.js version
- Shims dynamically set PATH; no static symlinks are used
EOF

# Replace placeholders in documentation
sed -i "s|LANG_BASE_DIR|$LANG_BASE_DIR|g" "$LANG_BASE_DIR/node/llm.txt"
sed -i "s|BIN_DIR|$BIN_DIR|g" "$LANG_BASE_DIR/node/llm.txt"
sed -i "s|NODE_VERSION|$NODE_VERSION|g" "$LANG_BASE_DIR/node/llm.txt"

echo ""
echo "✅ Node.js $NODE_VERSION installed successfully!"
echo "   - Installation directory: $NVM_DIR"
echo "   - Binaries available in: $BIN_DIR"
echo "   - Default version: $NODE_VERSION"
echo "   - Documentation: $LANG_BASE_DIR/node/llm.txt"
echo ""
echo "Managing Node.js versions:"
echo "   nvm-helper install <version>  - Install a Node.js version"
echo "   nvm-helper list              - List installed versions"
echo "   nvm-helper use <version>     - Switch to a version"
echo ""
echo "Or use nvm directly after sourcing:"
echo "   export NVM_DIR=\"$NVM_DIR\""
echo "   [ -s \"\$NVM_DIR/nvm.sh\" ] && \\. \"\$NVM_DIR/nvm.sh\""
echo "   nvm install 18.17.0"
echo "   nvm use 18.17.0"