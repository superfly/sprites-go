#!/bin/bash
set -e

echo "=========================================="
echo "Installing Erlang (canonical kerl approach)..."
echo "=========================================="

# Configuration with argument support
BASE_DIR="${1:-/opt}"  # Default to /opt, can be overridden with first argument
LANG_BASE_DIR="$BASE_DIR/languages"
BIN_DIR="$BASE_DIR/bin"
ETC_DIR="$BASE_DIR/etc/profile.d"

# Erlang specific configuration
ERLANG_VERSION="${ERLANG_VERSION:-27.0}"
KERL_ROOT="$LANG_BASE_DIR/erlang/kerl"
KERL_BUILD_DIR="$KERL_ROOT/builds"
KERL_INSTALL_DIR="$KERL_ROOT/installs"
KERL_DOWNLOAD_DIR="$KERL_ROOT/archives"

echo "Installing kerl and Erlang..."
echo "Base directory: $BASE_DIR"
echo "Default version: $ERLANG_VERSION"

# Note: Build dependencies should be installed in the base image:
# build-essential autoconf libncurses5-dev libssl-dev libwxgtk3.0-gtk3-dev
# libgl1-mesa-dev libglu1-mesa-dev libpng-dev libssh-dev unixodbc-dev
# xsltproc fop libxml2-utils libncurses-dev openjdk-11-jdk

# Create directories with proper permissions
echo "Creating directories..."
mkdir -p "$KERL_ROOT" "$KERL_BUILD_DIR" "$KERL_INSTALL_DIR" "$KERL_DOWNLOAD_DIR" "$BIN_DIR" "$ETC_DIR"
chown -R $(id -u):$(id -g) "$LANG_BASE_DIR/erlang" "$BIN_DIR"

# Download and install kerl
echo "Downloading kerl..."
curl -o "$KERL_ROOT/kerl" https://raw.githubusercontent.com/kerl/kerl/master/kerl
chmod +x "$KERL_ROOT/kerl"

# Configure kerl
export KERL_BASE_DIR="$KERL_ROOT"
export KERL_BUILD_DIR="$KERL_BUILD_DIR"
export KERL_DOWNLOAD_DIR="$KERL_DOWNLOAD_DIR"
export KERL_DEFAULT_INSTALL_DIR="$KERL_INSTALL_DIR"

# Create kerl configuration file
echo "Creating kerl configuration..."
cat > "$KERL_ROOT/.kerlrc" << EOF
KERL_BASE_DIR="$KERL_ROOT"
KERL_BUILD_DIR="$KERL_BUILD_DIR"
KERL_DOWNLOAD_DIR="$KERL_DOWNLOAD_DIR"
KERL_DEFAULT_INSTALL_DIR="$KERL_INSTALL_DIR"
KERL_BUILD_DOCS=yes
EOF

# Update kerl list
echo "Updating kerl releases list..."
"$KERL_ROOT/kerl" update releases

# Build Erlang
echo "Building Erlang ${ERLANG_VERSION}..."
"$KERL_ROOT/kerl" build "$ERLANG_VERSION" "$ERLANG_VERSION"

# Install Erlang
echo "Installing Erlang ${ERLANG_VERSION}..."
"$KERL_ROOT/kerl" install "$ERLANG_VERSION" "$KERL_INSTALL_DIR/$ERLANG_VERSION"

# Activate Erlang
. "$KERL_INSTALL_DIR/$ERLANG_VERSION/activate"

# Create symlinks in BIN_DIR
echo "Creating symlinks in $BIN_DIR..."
# Symlink kerl binary
ln -sf "$KERL_ROOT/kerl" "$BIN_DIR/kerl"
echo "  Linked: kerl"

# Symlink Erlang binaries
ERLANG_BIN_PATH="$KERL_INSTALL_DIR/$ERLANG_VERSION/bin"
for binary in "$ERLANG_BIN_PATH"/{erl,erlc,escript,dialyzer,rebar3}; do
    if [ -f "$binary" ] && [ -x "$binary" ]; then
        binary_name=$(basename "$binary")
        ln -sf "$binary" "$BIN_DIR/$binary_name"
        echo "  Linked: $binary_name"
    fi
done

# Verify installation
echo ""
echo "Verifying Erlang installation..."
"$BIN_DIR/erl" -eval 'io:format("Erlang/OTP ~s~n", [erlang:system_info(otp_release)]), halt().' -noshell
"$BIN_DIR/kerl" list installations

# Test Erlang
echo ""
echo "Testing Erlang..."
"$BIN_DIR/erl" -eval 'io:format("Hello from Erlang/OTP ~s!~n", [erlang:system_info(otp_release)]), halt().' -noshell

# Create kerl helper script
echo ""
echo "Creating kerl helper script..."
tee $BIN_DIR/kerl-helper > /dev/null << 'SCRIPT_EOF'
#!/bin/bash
# Helper script for kerl operations

KERL_ROOT="REPLACE_KERL_ROOT"
KERL_BUILD_DIR="REPLACE_KERL_BUILD_DIR"
KERL_INSTALL_DIR="REPLACE_KERL_INSTALL_DIR"
KERL_DOWNLOAD_DIR="REPLACE_KERL_DOWNLOAD_DIR"
BIN_DIR="REPLACE_BIN_DIR"

export KERL_BASE_DIR="$KERL_ROOT"
export KERL_BUILD_DIR="$KERL_BUILD_DIR"
export KERL_DOWNLOAD_DIR="$KERL_DOWNLOAD_DIR"
export KERL_DEFAULT_INSTALL_DIR="$KERL_INSTALL_DIR"

case "$1" in
    install)
        version="$2"
        if [ -z "$version" ]; then
            echo "Usage: kerl-helper install <version>"
            echo "Example: kerl-helper install 26.2"
            exit 1
        fi
        
        # Build and install
        "$KERL_ROOT/kerl" build "$version" "$version"
        "$KERL_ROOT/kerl" install "$version" "$KERL_INSTALL_DIR/$version"
        
        echo "Erlang $version installed"
        echo "To use: kerl-helper activate $version"
        ;;
    list)
        echo "Installed Erlang versions:"
        "$KERL_ROOT/kerl" list installations
        echo ""
        echo "Available releases:"
        "$KERL_ROOT/kerl" list releases | tail -10
        echo "(showing last 10 releases, use 'kerl list releases' for full list)"
        ;;
    activate)
        version="$2"
        if [ -z "$version" ]; then
            echo "Usage: kerl-helper activate <version>"
            echo "Example: kerl-helper activate 26.2"
            exit 1
        fi
        
        if [ ! -d "$KERL_INSTALL_DIR/$version" ]; then
            echo "Error: Erlang $version is not installed"
            echo "Run: kerl-helper install $version"
            exit 1
        fi
        
        # Update symlinks
        ERLANG_BIN_PATH="$KERL_INSTALL_DIR/$version/bin"
        for binary in "$ERLANG_BIN_PATH"/{erl,erlc,escript,dialyzer,rebar3}; do
            if [ -f "$binary" ] && [ -x "$binary" ]; then
                binary_name=$(basename "$binary")
                ln -sf "$binary" "$BIN_DIR/$binary_name"
            fi
        done
        
        echo "Erlang $version activated"
        echo "Symlinks updated in $BIN_DIR"
        echo ""
        echo "To activate in current shell, run:"
        echo "  . $KERL_INSTALL_DIR/$version/activate"
        ;;
    update)
        echo "Updating kerl releases list..."
        "$KERL_ROOT/kerl" update releases
        echo "Done. Use 'kerl-helper list' to see available releases"
        ;;
    *)
        echo "Erlang version manager (kerl) helper"
        echo ""
        echo "Usage: kerl-helper <command> [args]"
        echo ""
        echo "Commands:"
        echo "  install <version>  - Build and install an Erlang version"
        echo "  list              - List installed and available versions"
        echo "  activate <version> - Switch to a specific version"
        echo "  update            - Update the list of available releases"
        echo ""
        echo "Examples:"
        echo "  kerl-helper install 26.2"
        echo "  kerl-helper list"
        echo "  kerl-helper activate 26.2"
        ;;
esac
SCRIPT_EOF

# Replace placeholders in the helper script
sed -i "s|REPLACE_KERL_ROOT|$KERL_ROOT|g" $BIN_DIR/kerl-helper
sed -i "s|REPLACE_KERL_BUILD_DIR|$KERL_BUILD_DIR|g" $BIN_DIR/kerl-helper
sed -i "s|REPLACE_KERL_INSTALL_DIR|$KERL_INSTALL_DIR|g" $BIN_DIR/kerl-helper
sed -i "s|REPLACE_KERL_DOWNLOAD_DIR|$KERL_DOWNLOAD_DIR|g" $BIN_DIR/kerl-helper
sed -i "s|REPLACE_BIN_DIR|$BIN_DIR|g" $BIN_DIR/kerl-helper
chmod +x $BIN_DIR/kerl-helper

# Create profile script
echo ""
echo "Creating Erlang/kerl environment configuration..."
tee $ETC_DIR/kerl.sh > /dev/null << EOF
# Erlang/kerl environment setup
export KERL_BASE_DIR="$KERL_ROOT"
export KERL_BUILD_DIR="$KERL_BUILD_DIR"
export KERL_DOWNLOAD_DIR="$KERL_DOWNLOAD_DIR"
export KERL_DEFAULT_INSTALL_DIR="$KERL_INSTALL_DIR"
# Activate default Erlang version
[ -f "$KERL_INSTALL_DIR/$ERLANG_VERSION/activate" ] && . "$KERL_INSTALL_DIR/$ERLANG_VERSION/activate"
# PATH should already include $BIN_DIR from elsewhere
EOF

# Create documentation
echo ""
echo "Creating Erlang documentation..."
cat > "$LANG_BASE_DIR/erlang/llm.txt" << 'EOF'
Erlang Installation (via kerl)
==============================

This installation uses kerl for managing Erlang/OTP versions.

Installation Location:
- kerl: LANG_BASE_DIR/erlang/kerl
- Builds: LANG_BASE_DIR/erlang/kerl/builds
- Installs: LANG_BASE_DIR/erlang/kerl/installs
- Binaries: BIN_DIR (symlinked from active version)

Default Version: ERLANG_VERSION

Using Erlang:
-------------
The default Erlang version is immediately available:
  erl                         # Start Erlang shell
  erlc file.erl               # Compile Erlang file
  escript script.erl          # Run Erlang script
  dialyzer                    # Static analysis tool

Managing Versions:
------------------
Option 1: Use the helper script (recommended):
  kerl-helper install 26.2    # Install a new version
  kerl-helper list            # List installed/available versions
  kerl-helper activate 26.2   # Switch version & update symlinks
  kerl-helper update          # Update available releases list

Option 2: Use kerl directly:
  kerl build 26.2 26.2
  kerl install 26.2 KERL_INSTALL_DIR/26.2
  . KERL_INSTALL_DIR/26.2/activate

Common Erlang Commands:
-----------------------
Starting the shell:
  erl                         # Interactive shell
  erl -name mynode@host       # Named node
  erl -sname mynode           # Short name node

Compiling:
  erlc mymodule.erl           # Compile module
  erlc +debug_info mymod.erl  # With debug info
  c(mymodule).                # Compile from shell

Running scripts:
  escript myscript.erl        # Run Erlang script
  erl -noshell -s module func -s init stop

Shell commands:
  q().                        # Quit shell
  c(module).                  # Compile and load
  l(module).                  # Load module
  m(module).                  # Module info
  i().                        # Process info
  help().                     # Help

Rebar3 (if installed):
  rebar3 new app myapp        # Create new app
  rebar3 compile              # Compile project
  rebar3 shell                # Start shell with deps
  rebar3 release              # Build release

Environment Variables:
----------------------
KERL_BASE_DIR               # kerl base directory
ERL_AFLAGS                  # Additional flags for erl
ERLC_OPTS                   # Compiler options
ERL_LIBS                    # Additional library paths

Notes:
------
- Each Erlang version is completely isolated
- Use kerl-helper to manage versions easily
- Default version is activated in new shells
- Activate script modifies PATH and other env vars
- Documentation is built with installations
- Common tools: dialyzer, observer, debugger
EOF

# Replace placeholders in documentation
sed -i "s|LANG_BASE_DIR|$LANG_BASE_DIR|g" "$LANG_BASE_DIR/erlang/llm.txt"
sed -i "s|BIN_DIR|$BIN_DIR|g" "$LANG_BASE_DIR/erlang/llm.txt"
sed -i "s|ERLANG_VERSION|$ERLANG_VERSION|g" "$LANG_BASE_DIR/erlang/llm.txt"
sed -i "s|KERL_INSTALL_DIR|$KERL_INSTALL_DIR|g" "$LANG_BASE_DIR/erlang/llm.txt"

echo ""
echo "✅ Erlang/OTP $ERLANG_VERSION installed successfully with kerl!"
echo "   - Installation directory: $KERL_ROOT"
echo "   - Binaries available in: $BIN_DIR"
echo "   - Active version: $ERLANG_VERSION"
echo "   - Documentation: $LANG_BASE_DIR/erlang/llm.txt"
echo ""
echo "Managing Erlang versions:"
echo "   kerl-helper install 26.2   - Install a new version"
echo "   kerl-helper list           - List installed/available versions"
echo "   kerl-helper activate 26.2  - Switch to a version"
echo ""
echo "Or use kerl directly:"
echo "   $KERL_ROOT/kerl build 26.2 26.2"
echo "   $KERL_ROOT/kerl install 26.2" 