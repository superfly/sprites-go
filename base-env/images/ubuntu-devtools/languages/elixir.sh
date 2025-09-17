#!/bin/bash
set -e

echo "=========================================="
echo "Installing Elixir (prebuilt binary approach)..."
echo "=========================================="

# Configuration with argument support
BASE_DIR="${1:-/opt}"  # Default to /opt, can be overridden with first argument
LANG_BASE_DIR="$BASE_DIR/languages"
BIN_DIR="$BASE_DIR/bin"
ETC_DIR="$BASE_DIR/etc/profile.d"

# Elixir specific configuration
ELIXIR_VERSION="${ELIXIR_VERSION:-1.18.4}"
OTP_VERSION="${OTP_VERSION:-27}"
ELIXIR_ROOT="$LANG_BASE_DIR/elixir"
ELIXIR_INSTALL_DIR="$ELIXIR_ROOT/elixir-${ELIXIR_VERSION}-otp-${OTP_VERSION}"

echo "Installing Elixir..."
echo "Base directory: $BASE_DIR"
echo "Default version: $ELIXIR_VERSION (OTP $OTP_VERSION)"

# Note: Erlang must be installed first! Elixir runs on the Erlang VM.
# Make sure erlang.sh has been run before this script.

# Create directories with proper permissions
echo "Creating directories..."
mkdir -p "$ELIXIR_ROOT" "$BIN_DIR" "$ETC_DIR"
chown -R $(id -u):$(id -g) "$LANG_BASE_DIR/elixir" "$BIN_DIR"

# Ensure Erlang is available
if ! command -v erl >/dev/null 2>&1; then
    echo "Error: Erlang is not installed. Please install Erlang first."
    exit 1
fi

# Check Erlang version
echo "Checking Erlang/OTP version..."
ERLANG_OTP_VERSION=$(erl -eval 'io:format("~s", [erlang:system_info(otp_release)]), halt().' -noshell)
echo "Found Erlang/OTP $ERLANG_OTP_VERSION"

# Download prebuilt Elixir
echo "Downloading Elixir ${ELIXIR_VERSION} (prebuilt for OTP ${OTP_VERSION})..."
ELIXIR_URL="https://github.com/elixir-lang/elixir/releases/download/v${ELIXIR_VERSION}/elixir-otp-${OTP_VERSION}.zip"
curl -L -o "/tmp/elixir-${ELIXIR_VERSION}.zip" "$ELIXIR_URL"

# Extract Elixir
echo "Extracting Elixir..."
mkdir -p "$ELIXIR_INSTALL_DIR"
unzip -q "/tmp/elixir-${ELIXIR_VERSION}.zip" -d "$ELIXIR_INSTALL_DIR"
rm "/tmp/elixir-${ELIXIR_VERSION}.zip"

# Make binaries executable
chmod +x "$ELIXIR_INSTALL_DIR/bin"/*

# Create wrapper scripts in BIN_DIR
echo "Creating wrapper scripts in $BIN_DIR..."
for binary in elixir elixirc iex mix; do
    if [ -f "$ELIXIR_INSTALL_DIR/bin/$binary" ]; then
        cat > "$BIN_DIR/$binary" << EOF
#!/bin/bash
# Wrapper script for $binary
# Ensures Elixir bin directory is in PATH
export PATH="$ELIXIR_INSTALL_DIR/bin:\$PATH"
exec "$ELIXIR_INSTALL_DIR/bin/$binary" "\$@"
EOF
        chmod +x "$BIN_DIR/$binary"
        echo "  Created wrapper: $binary"
    fi
done

# Set up environment for mix commands
export PATH="$BIN_DIR:$PATH"
export MIX_HOME="$LANG_BASE_DIR/elixir/.mix"

# Install Hex package manager
echo "Installing Hex package manager..."
"$BIN_DIR/mix" local.hex --force

# Install rebar3 (Erlang build tool, used by some dependencies)
echo "Installing rebar3..."
"$BIN_DIR/mix" local.rebar --force

# Verify installation
echo ""
echo "Verifying Elixir installation..."
"$BIN_DIR/elixir" --version
"$BIN_DIR/mix" --version

# Test Elixir
echo ""
echo "Testing Elixir..."
"$BIN_DIR/elixir" -e 'IO.puts("Hello from Elixir #{System.version()}!")'

# Create version management helper script
echo ""
echo "Creating elixir-version helper script..."
tee $BIN_DIR/elixir-version > /dev/null << 'SCRIPT_EOF'
#!/bin/bash
# Helper script for Elixir version management

LANG_BASE_DIR="REPLACE_LANG_BASE_DIR"
BIN_DIR="REPLACE_BIN_DIR"
CURRENT_VERSION_FILE="$LANG_BASE_DIR/elixir/.current-version"

case "$1" in
    install)
        version="$2"
        otp_version="${3:-27}"  # Default to OTP 27 if not specified
        if [ -z "$version" ]; then
            echo "Usage: elixir-version install <version> [otp_version]"
            echo "Example: elixir-version install 1.17.0 26"
            exit 1
        fi
        
        install_dir="$LANG_BASE_DIR/elixir/elixir-${version}-otp-${otp_version}"
        if [ -d "$install_dir" ]; then
            echo "Elixir $version (OTP $otp_version) is already installed"
            exit 0
        fi
        
        echo "Downloading Elixir ${version} (prebuilt for OTP ${otp_version})..."
        url="https://github.com/elixir-lang/elixir/releases/download/v${version}/elixir-otp-${otp_version}.zip"
        curl -L -o "/tmp/elixir-${version}.zip" "$url" || {
            echo "Failed to download Elixir $version for OTP $otp_version"
            echo "Check if this combination exists at: https://github.com/elixir-lang/elixir/releases"
            exit 1
        }
        
        echo "Extracting Elixir..."
        mkdir -p "$install_dir"
        unzip -q "/tmp/elixir-${version}.zip" -d "$install_dir"
        rm "/tmp/elixir-${version}.zip"
        chmod +x "$install_dir/bin"/*
        
        echo "Elixir $version (OTP $otp_version) installed successfully"
        echo "To use: elixir-version use $version $otp_version"
        ;;
    list)
        echo "Installed Elixir versions:"
        for dir in "$LANG_BASE_DIR/elixir"/elixir-*-otp-*; do
            if [ -d "$dir" ]; then
                version_info=$(basename "$dir" | sed 's/elixir-//')
                if [ -f "$CURRENT_VERSION_FILE" ] && [ "$(cat "$CURRENT_VERSION_FILE")" = "$(basename "$dir")" ]; then
                    echo "* $version_info (current)"
                else
                    echo "  $version_info"
                fi
            fi
        done
        ;;
    use)
        version="$2"
        otp_version="${3:-27}"
        if [ -z "$version" ]; then
            echo "Usage: elixir-version use <version> [otp_version]"
            echo "Example: elixir-version use 1.17.0 26"
            exit 1
        fi
        
        install_dir="$LANG_BASE_DIR/elixir/elixir-${version}-otp-${otp_version}"
        if [ ! -d "$install_dir" ]; then
            echo "Elixir $version (OTP $otp_version) is not installed"
            echo "Run: elixir-version install $version $otp_version"
            exit 1
        fi
        
        # Update wrapper scripts
        for binary in elixir elixirc iex mix; do
            if [ -f "$install_dir/bin/$binary" ]; then
                cat > "$BIN_DIR/$binary" << WRAPPER_EOF
#!/bin/bash
# Wrapper script for $binary
# Ensures Elixir bin directory is in PATH
export PATH="$install_dir/bin:\\\$PATH"
exec "$install_dir/bin/$binary" "\\\$@"
WRAPPER_EOF
                chmod +x "$BIN_DIR/$binary"
            fi
        done
        
        # Save current version
        echo "elixir-${version}-otp-${otp_version}" > "$CURRENT_VERSION_FILE"
        
        echo "Now using Elixir $version (OTP $otp_version)"
        ;;
    current)
        if [ -f "$CURRENT_VERSION_FILE" ]; then
            current=$(cat "$CURRENT_VERSION_FILE" | sed 's/elixir-//')
            echo "Current: $current"
        else
            echo "No Elixir version set"
        fi
        ;;
    *)
        echo "Elixir version manager"
        echo ""
        echo "Usage: elixir-version <command> [args]"
        echo ""
        echo "Commands:"
        echo "  install <version> [otp]  - Install an Elixir version"
        echo "  list                     - List installed versions"
        echo "  use <version> [otp]      - Switch to a specific version"
        echo "  current                  - Show current version"
        echo ""
        echo "Examples:"
        echo "  elixir-version install 1.17.0 26"
        echo "  elixir-version list"
        echo "  elixir-version use 1.17.0 26"
        ;;
esac
SCRIPT_EOF

# Replace placeholders in the helper script
sed -i "s|REPLACE_LANG_BASE_DIR|$LANG_BASE_DIR|g" $BIN_DIR/elixir-version
sed -i "s|REPLACE_BIN_DIR|$BIN_DIR|g" $BIN_DIR/elixir-version
chmod +x $BIN_DIR/elixir-version

# Save current version info
echo "elixir-${ELIXIR_VERSION}-otp-${OTP_VERSION}" > "$ELIXIR_ROOT/.current-version"

# Create profile script
echo ""
echo "Creating Elixir environment configuration..."
tee $ETC_DIR/elixir.sh > /dev/null << EOF
# Elixir environment setup
export MIX_HOME="$LANG_BASE_DIR/elixir/.mix"
export HEX_HOME="$LANG_BASE_DIR/elixir/.hex"
# PATH should already include $BIN_DIR from elsewhere
EOF

# Create documentation
echo ""
echo "Creating Elixir documentation..."
cat > "$LANG_BASE_DIR/elixir/llm.txt" << 'EOF'
Elixir Installation (prebuilt binaries)
=======================================

This installation uses prebuilt Elixir binaries from the official releases.

Installation Location:
- Elixir versions: LANG_BASE_DIR/elixir/elixir-VERSION-otp-OTP
- Binaries: BIN_DIR (symlinked from active version)
- Mix home: LANG_BASE_DIR/elixir/.mix
- Hex home: LANG_BASE_DIR/elixir/.hex

Default Version: ELIXIR_VERSION (OTP OTP_VERSION)

Prerequisites:
--------------
Erlang/OTP must be installed! Elixir runs on the Erlang VM.
Make sure the OTP version matches the Elixir build.

Using Elixir:
-------------
The default Elixir version is immediately available:
  elixir --version            # Check version
  iex                         # Interactive shell
  mix new myapp               # Create new project
  mix compile                 # Compile project
  mix test                    # Run tests

Managing Versions:
------------------
Use the elixir-version helper script:
  elixir-version install 1.17.0 26   # Install Elixir 1.17.0 for OTP 26
  elixir-version list                # List installed versions
  elixir-version use 1.17.0 26       # Switch to a specific version
  elixir-version current             # Show current version

Note: You need to specify the OTP version when installing/using Elixir
versions to ensure compatibility with your Erlang installation.

Common Mix Commands:
--------------------
Project management:
  mix new myapp               # Create new project
  mix new myapp --sup         # With supervisor
  mix phoenix.new webapp      # Phoenix web app (if installed)

Dependencies:
  mix deps.get                # Fetch dependencies
  mix deps.update --all       # Update all deps
  mix deps.tree               # Show dependency tree

Development:
  mix compile                 # Compile project
  mix test                    # Run tests
  mix test --cover            # With coverage
  mix format                  # Format code
  mix dialyzer                # Static analysis (if installed)
  mix docs                    # Generate docs

Running:
  mix run                     # Run project
  mix run --no-halt           # Keep running
  iex -S mix                  # Interactive shell with project

Phoenix (if installed):
  mix phx.server              # Start Phoenix server
  mix phx.routes              # Show routes
  mix ecto.create             # Create database
  mix ecto.migrate            # Run migrations

Common IEx Commands:
--------------------
h Module.function           # Help for function
r Module                    # Reload module
c "file.ex"                 # Compile file
i variable                  # Inspect variable
v                           # Last result
v(n)                        # Result n steps back
:observer.start()           # Start observer GUI (if available)

Environment Variables:
----------------------
MIX_ENV                     # Mix environment (dev/test/prod)
MIX_HOME                    # Mix archives and config
HEX_HOME                    # Hex packages cache
ERL_AFLAGS                  # Erlang VM flags

Notes:
------
- Each Elixir version is isolated
- Elixir must match the installed Erlang/OTP version
- Use .tool-versions for project-specific versions
- Hex and rebar are installed globally in MIX_HOME
- Mix tasks are available after running 'mix deps.get'
EOF

# Replace placeholders in documentation
sed -i "s|LANG_BASE_DIR|$LANG_BASE_DIR|g" "$LANG_BASE_DIR/elixir/llm.txt"
sed -i "s|BIN_DIR|$BIN_DIR|g" "$LANG_BASE_DIR/elixir/llm.txt"
sed -i "s|ELIXIR_VERSION|$ELIXIR_VERSION|g" "$LANG_BASE_DIR/elixir/llm.txt"
sed -i "s|OTP_VERSION|$OTP_VERSION|g" "$LANG_BASE_DIR/elixir/llm.txt"

echo ""
echo "✅ Elixir $ELIXIR_VERSION installed successfully!"
echo "   - Installation directory: $ELIXIR_INSTALL_DIR"
echo "   - Binaries available in: $BIN_DIR"
echo "   - Version: $ELIXIR_VERSION (OTP $OTP_VERSION)"
echo "   - Documentation: $LANG_BASE_DIR/elixir/llm.txt"
echo ""
echo "Managing Elixir versions:"
echo "   elixir-version install 1.17.0 26  - Install Elixir for specific OTP"
echo "   elixir-version list               - List installed versions"
echo "   elixir-version use 1.17.0 26      - Switch to a version"
echo ""
echo "Note: Elixir versions must match your Erlang/OTP version."
echo "Check available combinations at:"
echo "https://github.com/elixir-lang/elixir/releases"