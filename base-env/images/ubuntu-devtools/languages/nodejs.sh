#!/bin/bash
set -e

echo "=========================================="
echo "Installing Node.js (canonical nvm approach)..."
echo "=========================================="

# Configuration with argument support
BASE_DIR="${1:-/opt}"  # Default to /opt, can be overridden with first argument
LANG_BASE_DIR="$BASE_DIR/languages"
BIN_DIR="$BASE_DIR/bin"
ETC_DIR="$BASE_DIR/etc/profile.d"

# Node.js specific configuration
NODE_VERSION="${NODE_VERSION:-20.18.0}"
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

# Create symlinks in BIN_DIR
echo "Creating symlinks in $BIN_DIR..."
NODE_BIN_PATH="$(dirname $(which node))"
for binary in "$NODE_BIN_PATH"/{node,npm,npx,corepack}; do
    if [ -f "$binary" ] && [ -x "$binary" ]; then
        binary_name=$(basename "$binary")
        ln -sf "$binary" "$BIN_DIR/$binary_name"
        echo "  Linked: $binary_name"
    fi
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

# Create nvm helper script
echo ""
echo "Creating nvm helper script..."
tee $BIN_DIR/nvm-helper > /dev/null << 'SCRIPT_EOF'
#!/bin/bash
# Helper script for nvm operations

NVM_DIR="REPLACE_NVM_DIR"
BIN_DIR="REPLACE_BIN_DIR"

export NVM_DIR="$NVM_DIR"
[ -s "$NVM_DIR/nvm.sh" ] && \. "$NVM_DIR/nvm.sh"

case "$1" in
    install)
        version="$2"
        if [ -z "$version" ]; then
            echo "Usage: nvm-helper install <version>"
            echo "Example: nvm-helper install 18.17.0"
            exit 1
        fi
        
        nvm install "$version"
        
        # Update symlinks if this is now the default
        if nvm use "$version" &>/dev/null; then
            NODE_BIN_PATH="$(dirname $(which node))"
            for binary in "$NODE_BIN_PATH"/{node,npm,npx,corepack}; do
                if [ -f "$binary" ] && [ -x "$binary" ]; then
                    binary_name=$(basename "$binary")
                    ln -sf "$binary" "$BIN_DIR/$binary_name"
                fi
            done
        fi
        ;;
    list)
        nvm list
        ;;
    use)
        version="$2"
        if [ -z "$version" ]; then
            echo "Usage: nvm-helper use <version>"
            echo "Example: nvm-helper use 18.17.0"
            exit 1
        fi
        
        nvm use "$version"
        
        # Update symlinks
        NODE_BIN_PATH="$(dirname $(which node))"
        for binary in "$NODE_BIN_PATH"/{node,npm,npx,corepack}; do
            if [ -f "$binary" ] && [ -x "$binary" ]; then
                binary_name=$(basename "$binary")
                ln -sf "$binary" "$BIN_DIR/$binary_name"
            fi
        done
        echo "Symlinks updated in $BIN_DIR"
        ;;
    *)
        echo "Node.js version manager (nvm) helper"
        echo ""
        echo "Usage: nvm-helper <command> [args]"
        echo ""
        echo "Commands:"
        echo "  install <version>  - Install a Node.js version"
        echo "  list              - List installed versions"
        echo "  use <version>     - Switch to a specific version"
        echo ""
        echo "Examples:"
        echo "  nvm-helper install 18.17.0"
        echo "  nvm-helper list"
        echo "  nvm-helper use 18.17.0"
        ;;
esac
SCRIPT_EOF

# Replace placeholders in the helper script
sed -i "s|REPLACE_NVM_DIR|$NVM_DIR|g" $BIN_DIR/nvm-helper
sed -i "s|REPLACE_BIN_DIR|$BIN_DIR|g" $BIN_DIR/nvm-helper
chmod +x $BIN_DIR/nvm-helper

# Create profile script
echo ""
echo "Creating Node.js/nvm environment configuration..."
tee $ETC_DIR/nvm.sh > /dev/null << EOF
# Node.js/nvm environment setup
export NVM_DIR="$NVM_DIR"
[ -s "\$NVM_DIR/nvm.sh" ] && \. "\$NVM_DIR/nvm.sh"  # This loads nvm
[ -s "\$NVM_DIR/bash_completion" ] && \. "\$NVM_DIR/bash_completion"  # This loads nvm bash_completion
# Configure npm cache location
export NPM_CONFIG_CACHE="$LANG_BASE_DIR/node/.npm-cache"
# PATH should already include $BIN_DIR from elsewhere
EOF

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
- The helper script automatically updates symlinks when switching versions
- Symlinks in BIN_DIR always point to the active version
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