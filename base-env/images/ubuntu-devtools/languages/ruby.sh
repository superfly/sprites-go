#!/bin/bash
set -e

# Implementation notes:
# See ./llm.txt in this directory for the filesystem layout and shim standard
# that other languages should follow (manager-first install, nvm-style shims).
# conforms to llm.txt and matches node layout

echo "=========================================="
echo "Installing Ruby (canonical rbenv approach)..."
echo "=========================================="

# Configuration with argument support
BASE_DIR="${1:-/opt}"  # Default to /opt, can be overridden with first argument
LANG_BASE_DIR="$BASE_DIR/languages"
BIN_DIR="$BASE_DIR/bin"
ETC_DIR="$BASE_DIR/etc/profile.d"

# Ruby specific configuration
# Baseline pinned version as of 2025-10-04: 3.4.6
RUBY_VERSION="${RUBY_VERSION:-3.4.6}"
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

# Setup rbenv environment (no shell eval)
export RBENV_ROOT="$RBENV_ROOT"
export PATH="$RBENV_ROOT/bin:$PATH"
RBENV_BIN="$RBENV_ROOT/bin/rbenv"

# Install Ruby using explicit rbenv binary
echo "Installing Ruby ${RUBY_VERSION}..."
"$RBENV_BIN" install "$RUBY_VERSION"
"$RBENV_BIN" global "$RUBY_VERSION"
"$RBENV_BIN" rehash

# Update RubyGems via shim directly
echo "Updating RubyGems..."
"$RBENV_ROOT/shims/gem" update --system

# Install bundler
echo "Installing bundler..."
"$RBENV_ROOT/shims/gem" install bundler

# Clean Ruby build artifacts and gem caches
echo "Cleaning Ruby caches..."
rm -rf "$RBENV_ROOT/sources" 2>/dev/null || true
"$RBENV_ROOT/shims/gem" cleanup --silent || true

# Create wrapper shims in BIN_DIR for core Ruby commands
echo "Creating rbenv-enabled shims in $BIN_DIR..."
for cmd in ruby gem bundle bundler irb rake rbenv; do
    cat > "$BIN_DIR/$cmd" << 'WRAP_EOF'
#!/bin/bash
set -e

# rbenv-enabled shim that ensures active Ruby is available
DEFAULT_RBENV_ROOT="REPLACE_RBENV_ROOT"

export RBENV_ROOT="${RBENV_ROOT:-$DEFAULT_RBENV_ROOT}"

# Ensure rbenv bin and shims are on PATH
case ":$PATH:" in
  *":$RBENV_ROOT/bin:") ;;
  *) PATH="$RBENV_ROOT/bin:$PATH" ;;
esac
case ":$PATH:" in
  *":$RBENV_ROOT/shims:") ;;
  *) PATH="$RBENV_ROOT/shims:$PATH" ;;
esac

cmd_name="$(basename "$0")"
if [ "$cmd_name" = "rbenv" ]; then
  exec "$RBENV_ROOT/bin/rbenv" "$@"
else
  exec "$RBENV_ROOT/shims/$cmd_name" "$@"
fi
WRAP_EOF
    sed -i "s|REPLACE_RBENV_ROOT|$RBENV_ROOT|g" "$BIN_DIR/$cmd"
    chmod +x "$BIN_DIR/$cmd"
    echo "  Created shim: $cmd"
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

## No helper script; rbenv is invoked via shims
## No profile script; shims ensure PATH dynamically

# Create documentation
echo ""
echo "Creating Ruby documentation..."
cat > "$LANG_BASE_DIR/ruby/llm.txt" << 'EOF'
Ruby Installation (via rbenv)
=============================

This installation uses rbenv for managing Ruby versions.

Installation Location:
- rbenv: LANG_BASE_DIR/ruby/rbenv
- Binaries: BIN_DIR (shim wrappers)
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
Use rbenv directly (shims handle PATH at runtime):
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
- Shims dynamically set PATH; no shell profile scripts are modified
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
echo "Shims provided for: ruby, gem, bundle, bundler, irb, rake, rbenv"