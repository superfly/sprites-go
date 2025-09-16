#!/bin/bash
set -e

echo "=========================================="
echo "Installing Ruby (canonical rbenv approach)..."
echo "=========================================="

# Configuration with argument support
BASE_DIR="${1:-/opt}"  # Default to /opt, can be overridden with first argument
LANG_BASE_DIR="$BASE_DIR/languages"
BIN_DIR="$BASE_DIR/bin"
ETC_DIR="$BASE_DIR/etc/profile.d"

# Ruby specific configuration
RUBY_VERSION="${RUBY_VERSION:-3.3.5}"
RBENV_ROOT="$LANG_BASE_DIR/ruby/rbenv"

echo "Installing rbenv and Ruby..."
echo "Base directory: $BASE_DIR"
echo "Default version: $RUBY_VERSION"

# Note: Build dependencies should be installed in the base image:
# build-essential libssl-dev libreadline-dev zlib1g-dev libncurses5-dev
# libffi-dev libgdbm-dev libyaml-dev

# Create directories with proper permissions
echo "Creating directories..."
mkdir -p "$RBENV_ROOT" "$BIN_DIR" "$ETC_DIR"
chown -R $(id -u):$(id -g) "$LANG_BASE_DIR/ruby" "$BIN_DIR"

# Install rbenv
echo "Installing rbenv..."
git clone https://github.com/rbenv/rbenv.git "$RBENV_ROOT"
cd "$RBENV_ROOT" && src/configure && make -C src

# Install ruby-build as rbenv plugin
echo "Installing ruby-build plugin..."
mkdir -p "$RBENV_ROOT/plugins"
git clone https://github.com/rbenv/ruby-build.git "$RBENV_ROOT/plugins/ruby-build"

# Remove .git directories to save space (readonly installation)
rm -rf "$RBENV_ROOT/.git"
rm -rf "$RBENV_ROOT/plugins/ruby-build/.git"

# Setup rbenv environment
export RBENV_ROOT="$RBENV_ROOT"
export PATH="$RBENV_ROOT/bin:$PATH"
eval "$(rbenv init -)"

# Install Ruby
echo "Installing Ruby ${RUBY_VERSION}..."
rbenv install "$RUBY_VERSION"
rbenv global "$RUBY_VERSION"

# Update RubyGems
echo "Updating RubyGems..."
gem update --system

# Install bundler
echo "Installing bundler..."
gem install bundler

# Create symlinks in BIN_DIR
echo "Creating symlinks in $BIN_DIR..."
for binary in "$RBENV_ROOT/bin"/*; do
    if [ -f "$binary" ] && [ -x "$binary" ]; then
        binary_name=$(basename "$binary")
        ln -sf "$binary" "$BIN_DIR/$binary_name"
        echo "  Linked: $binary_name"
    fi
done

# Also symlink Ruby binaries from the shims directory
for binary in "$RBENV_ROOT/shims"/{ruby,gem,bundle,bundler,irb,rake}; do
    if [ -f "$binary" ] && [ -x "$binary" ]; then
        binary_name=$(basename "$binary")
        ln -sf "$binary" "$BIN_DIR/$binary_name"
        echo "  Linked: $binary_name"
    fi
done


# Verify installation
echo ""
echo "Verifying Ruby installation..."
"$BIN_DIR/ruby" --version
"$BIN_DIR/gem" --version
"$BIN_DIR/rbenv" --version

# Show installed versions
echo ""
echo "Installed Ruby versions:"
rbenv versions

# Test Ruby
echo ""
echo "Testing Ruby..."
"$BIN_DIR/ruby" -e "puts 'Hello from Ruby #{RUBY_VERSION}!'"

# Create rbenv helper script
echo ""
echo "Creating rbenv helper script..."
tee $BIN_DIR/rbenv-helper > /dev/null << 'SCRIPT_EOF'
#!/bin/bash
# Helper script for rbenv operations

RBENV_ROOT="REPLACE_RBENV_ROOT"
BIN_DIR="REPLACE_BIN_DIR"

export RBENV_ROOT="$RBENV_ROOT"
export PATH="$RBENV_ROOT/bin:$PATH"
eval "$(rbenv init -)"

case "$1" in
    install)
        version="$2"
        if [ -z "$version" ]; then
            echo "Usage: rbenv-helper install <version>"
            echo "Example: rbenv-helper install 3.2.0"
            exit 1
        fi
        
        rbenv install "$version"
        echo "Ruby $version installed"
        echo "To use: rbenv-helper global $version"
        ;;
    list)
        rbenv versions
        ;;
    global)
        version="$2"
        if [ -z "$version" ]; then
            echo "Usage: rbenv-helper global <version>"
            echo "Example: rbenv-helper global 3.2.0"
            exit 1
        fi
        
        rbenv global "$version"
        
        # Update symlinks
        for binary in "$RBENV_ROOT/shims"/{ruby,gem,bundle,bundler,irb,rake}; do
            if [ -f "$binary" ] && [ -x "$binary" ]; then
                binary_name=$(basename "$binary")
                ln -sf "$binary" "$BIN_DIR/$binary_name"
            fi
        done
        
        echo "Ruby $version is now the global default"
        echo "Symlinks updated in $BIN_DIR"
        ;;
    local)
        version="$2"
        if [ -z "$version" ]; then
            echo "Usage: rbenv-helper local <version>"
            echo "Example: rbenv-helper local 3.2.0"
            echo ""
            echo "This sets the Ruby version for the current directory"
            exit 1
        fi
        
        rbenv local "$version"
        echo "Ruby $version set for current directory"
        ;;
    *)
        echo "Ruby version manager (rbenv) helper"
        echo ""
        echo "Usage: rbenv-helper <command> [args]"
        echo ""
        echo "Commands:"
        echo "  install <version>  - Install a Ruby version"
        echo "  list              - List installed versions"
        echo "  global <version>  - Set global Ruby version"
        echo "  local <version>   - Set local Ruby version for current directory"
        echo ""
        echo "Examples:"
        echo "  rbenv-helper install 3.2.0"
        echo "  rbenv-helper list"
        echo "  rbenv-helper global 3.3.0"
        ;;
esac
SCRIPT_EOF

# Replace placeholders in the helper script
sed -i "s|REPLACE_RBENV_ROOT|$RBENV_ROOT|g" $BIN_DIR/rbenv-helper
sed -i "s|REPLACE_BIN_DIR|$BIN_DIR|g" $BIN_DIR/rbenv-helper
chmod +x $BIN_DIR/rbenv-helper

# Create profile script
echo ""
echo "Creating Ruby/rbenv environment configuration..."
tee $ETC_DIR/rbenv.sh > /dev/null << EOF
# Ruby/rbenv environment setup
export RBENV_ROOT="$RBENV_ROOT"
export PATH="\$RBENV_ROOT/bin:\$PATH"
eval "\$(rbenv init -)"
# Configure gem cache location
export GEM_HOME="\$RBENV_ROOT/versions/\$(rbenv version-name)/lib/ruby/gems"
export GEM_PATH="\$GEM_HOME"
# PATH should already include $BIN_DIR from elsewhere
EOF

# Create documentation
echo ""
echo "Creating Ruby documentation..."
cat > "$LANG_BASE_DIR/ruby/llm.txt" << 'EOF'
Ruby Installation (via rbenv)
=============================

This installation uses rbenv for managing Ruby versions.

Installation Location:
- rbenv: LANG_BASE_DIR/ruby/rbenv
- Binaries: BIN_DIR (symlinked from shims)
- Gems: Within each Ruby version

Default Version: RUBY_VERSION

Using Ruby:
-----------
The default Ruby version is immediately available:
  ruby --version
  gem --version
  irb
  bundle --version
  rake --version

Managing Versions:
------------------
Option 1: Use the helper script (no sourcing required):
  rbenv-helper install 3.2.0   # Install a new version
  rbenv-helper list            # List installed versions
  rbenv-helper global 3.2.0    # Set global default
  rbenv-helper local 3.1.0     # Set version for current directory

Option 2: Use rbenv directly (requires environment setup):
  rbenv install 3.2.0
  rbenv global 3.2.0
  rbenv local 3.1.0
  rbenv versions

Installing Gems:
----------------
Local gems (in project with Gemfile):
  bundle install
  bundle add rails

Global gems (for current Ruby version):
  gem install rails
  gem install puma

To install for all versions, switch versions and install:
  rbenv global 3.3.4 && gem install <gem>
  rbenv global 3.2.0 && gem install <gem>

Bundler is included by default in modern Ruby versions.

Common Commands:
----------------
ruby --version              # Check Ruby version
gem list                    # List installed gems
bundle init                 # Create Gemfile
bundle install              # Install dependencies
bundle exec <command>       # Run command with bundled gems
irb                         # Interactive Ruby shell
rake -T                     # List rake tasks

Environment Variables:
----------------------
RBENV_ROOT                  # rbenv installation directory
GEM_HOME                    # Where gems are installed
GEM_PATH                    # Gem search path
BUNDLE_PATH                 # Bundler install location

Notes:
------
- Each Ruby version has its own gems
- Use .ruby-version files in projects to specify Ruby version
- rbenv shims automatically select the right Ruby version
- The helper script updates symlinks when switching versions
- Bundler is the preferred way to manage project dependencies
EOF

# Replace placeholders in documentation
sed -i "s|LANG_BASE_DIR|$LANG_BASE_DIR|g" "$LANG_BASE_DIR/ruby/llm.txt"
sed -i "s|BIN_DIR|$BIN_DIR|g" "$LANG_BASE_DIR/ruby/llm.txt"
sed -i "s|RUBY_VERSION|$RUBY_VERSION|g" "$LANG_BASE_DIR/ruby/llm.txt"

echo ""
echo "✅ Ruby $RUBY_VERSION installed successfully with rbenv!"
echo "   - Installation directory: $RBENV_ROOT"
echo "   - Binaries available in: $BIN_DIR"
echo "   - Global version: $RUBY_VERSION"
echo "   - Documentation: $LANG_BASE_DIR/ruby/llm.txt"
echo ""
echo "Managing Ruby versions (canonical rbenv way):"
echo "   rbenv install <version>    - Install a Ruby version"
echo "   rbenv versions            - List installed versions"
echo "   rbenv global <version>    - Set global default"
echo "   rbenv local <version>     - Set version for current directory"
echo ""
echo "Helper commands (works without sourcing rbenv):"
echo "   rbenv-helper install 3.2.0"
echo "   rbenv-helper list"
echo "   rbenv-helper global 3.3.0"