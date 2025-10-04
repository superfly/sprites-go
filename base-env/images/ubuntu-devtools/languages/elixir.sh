#!/bin/bash
set -e

# conforms to llm.txt and matches node layout

echo "=========================================="
echo "Installing Elixir (precompiled + lightweight manager)..."
echo "=========================================="

# Configuration with argument support
BASE_DIR="${1:-/opt}"  # Default to /opt, can be overridden with first argument
LANG_BASE_DIR="$BASE_DIR/languages"
BIN_DIR="$BASE_DIR/bin"
ETC_DIR="$BASE_DIR/etc/profile.d"

# Elixir specific configuration
# Use a kiex-known Elixir release by default; override via ELIXIR_VERSION
# Baseline pinned version as of 2025-10-04: 1.18.4 (OTP 28)
ELIXIR_VERSION="${ELIXIR_VERSION:-1.18.4}"
OTP_VERSION="${OTP_VERSION:-28}"
ELIXIR_ROOT="$LANG_BASE_DIR/elixir"
KIEX_DIR="$ELIXIR_ROOT/kiex"

echo "Installing Elixir..."
echo "Base directory: $BASE_DIR"
echo "Default version: $ELIXIR_VERSION (OTP $OTP_VERSION)"

# Note: Erlang must be installed first! Elixir runs on the Erlang VM.
# Make sure erlang.sh has been run before this script.

# Create directories with proper permissions
echo "Creating directories..."
mkdir -p "$ELIXIR_ROOT" "$BIN_DIR"
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
VERSIONS_DIR="$ELIXIR_ROOT/versions"
ELIXIR_OTP_MAJOR="$ERLANG_OTP_VERSION"
INSTALL_DIR="$VERSIONS_DIR/$ELIXIR_VERSION-otp-$ELIXIR_OTP_MAJOR"

echo "Downloading precompiled Elixir $ELIXIR_VERSION for OTP $ELIXIR_OTP_MAJOR..."
mkdir -p "$INSTALL_DIR"

TMP_ZIP="/tmp/elixir-precompiled.zip"
set +e
curl -fsSL "https://repo.hex.pm/builds/elixir/v$ELIXIR_VERSION-otp-$ELIXIR_OTP_MAJOR.zip" -o "$TMP_ZIP" || \
curl -fsSL "https://github.com/elixir-lang/elixir/releases/download/v$ELIXIR_VERSION/elixir-otp-$ELIXIR_OTP_MAJOR.zip" -o "$TMP_ZIP" || \
curl -fsSL "https://github.com/elixir-lang/elixir/releases/download/v$ELIXIR_VERSION/Precompiled.zip" -o "$TMP_ZIP"
rc=$?
set -e
if [ $rc -ne 0 ] || [ ! -s "$TMP_ZIP" ]; then
    echo "Failed to download precompiled Elixir for version $ELIXIR_VERSION (OTP $ELIXIR_OTP_MAJOR)."
    exit 1
fi

unzip -q "$TMP_ZIP" -d "$INSTALL_DIR"
rm -f "$TMP_ZIP"

# Set current symlink
ln -sfn "$INSTALL_DIR" "$ELIXIR_ROOT/current"

echo "Creating shims in $BIN_DIR..."
for cmd in elixir elixirc iex mix; do
    cat > "$BIN_DIR/$cmd" << 'WRAP_EOF'
#!/bin/sh
set -e

DEFAULT_ELIXIR_CURRENT="REPLACE_ELIXIR_CURRENT"
BIN_PATH="$DEFAULT_ELIXIR_CURRENT/bin"

case ":$PATH:" in
  *":$BIN_PATH:") ;;
  *) PATH="$BIN_PATH:$PATH" ;;
esac

exec "$BIN_PATH/$(basename "$0")" "$@"
WRAP_EOF
    sed -i "s|REPLACE_ELIXIR_CURRENT|$ELIXIR_ROOT/current|g" "$BIN_DIR/$cmd"
    chmod +x "$BIN_DIR/$cmd"
    echo "  Created shim: $cmd"
done

export PATH="$BIN_DIR:$PATH"
export MIX_HOME="$LANG_BASE_DIR/elixir/.mix"
export HEX_HOME="$LANG_BASE_DIR/elixir/.hex"

# Install Hex and rebar3 for the default Elixir
echo "Installing Hex package manager..."
"$ELIXIR_ROOT/current/bin/mix" local.hex --force

echo "Installing rebar3..."
"$ELIXIR_ROOT/current/bin/mix" local.rebar --force

# Cleanup Mix/Hex build caches
echo "Cleaning Mix/Hex caches..."
rm -rf "$LANG_BASE_DIR/elixir/.mix/archives/tmp" "$LANG_BASE_DIR/elixir/.hex/httpreqs" 2>/dev/null || true

# Verify installation
echo ""
echo "Verifying Elixir installation..."
"$BIN_DIR/elixir" --version
"$BIN_DIR/mix" --version

# Test Elixir
echo ""
echo "Testing Elixir..."
"$BIN_DIR/elixir" -e 'IO.puts("Hello from Elixir #{System.version()}!")'

"$BIN_DIR/elixir" --version >/dev/null 2>&1 || true

# Create version management helper script (lightweight)
echo ""
echo "Creating elixir-version helper script..."
tee $BIN_DIR/elixir-version > /dev/null << 'SCRIPT_EOF'
#!/bin/bash
# Lightweight Elixir version manager (downloads precompiled archives)

set -e

ELIXIR_ROOT="REPLACE_ELIXIR_ROOT"
VERSIONS_DIR="$ELIXIR_ROOT/versions"

ensure_dirs() {
  mkdir -p "$VERSIONS_DIR"
}

download_and_install() {
  local version="$1"
  local otp_major
  otp_major=$(erl -eval 'io:format("~s", [erlang:system_info(otp_release)]), halt().' -noshell)
  local install_dir="$VERSIONS_DIR/$version-otp-$otp_major"
  local tmp_zip
  tmp_zip=$(mktemp)
  echo "Downloading Elixir $version for OTP $otp_major..."
  set +e
  curl -fsSL "https://repo.hex.pm/builds/elixir/v$version-otp-$otp_major.zip" -o "$tmp_zip" || \
  curl -fsSL "https://github.com/elixir-lang/elixir/releases/download/v$version/elixir-otp-$otp_major.zip" -o "$tmp_zip" || \
  curl -fsSL "https://github.com/elixir-lang/elixir/releases/download/v$version/Precompiled.zip" -o "$tmp_zip"
  local rc=$?
  set -e
  if [ $rc -ne 0 ] || [ ! -s "$tmp_zip" ]; then
    echo "Failed to download Elixir $version"
    exit 1
  fi
  mkdir -p "$install_dir"
  unzip -q "$tmp_zip" -d "$install_dir"
  rm -f "$tmp_zip"
  ln -sfn "$install_dir" "$ELIXIR_ROOT/current"
}

case "$1" in
  install)
    ensure_dirs
    if [ -z "$2" ]; then
      echo "Usage: elixir-version install <version>"
      exit 1
    fi
    download_and_install "$2"
    ;;
  use)
    ensure_dirs
    if [ -z "$2" ]; then
      echo "Usage: elixir-version use <version>"
      exit 1
    fi
    dest=$(ls -d "$VERSIONS_DIR/$2"* 2>/dev/null | head -n1)
    if [ -z "$dest" ]; then
      echo "Version $2 not installed"
      exit 1
    fi
    ln -sfn "$dest" "$ELIXIR_ROOT/current"
    ;;
  list)
    ensure_dirs
    ls -1 "$VERSIONS_DIR" || true
    ;;
  current)
    if [ -L "$ELIXIR_ROOT/current" ]; then
      readlink "$ELIXIR_ROOT/current"
    else
      echo "none"
    fi
    ;;
  *)
    echo "Elixir lightweight manager"
    echo "Usage: elixir-version <install|use|list|current> [args]"
    ;;
esac
SCRIPT_EOF
sed -i "s|REPLACE_ELIXIR_ROOT|$ELIXIR_ROOT|g" $BIN_DIR/elixir-version
chmod +x $BIN_DIR/elixir-version

## No separate versions/ layout; managed by kiex under $ELIXIR_ROOT/kiex

## No profile scripts; shims handle PATH at runtime per llm.txt

echo ""
echo "Creating Elixir documentation..."
cat > "$LANG_BASE_DIR/elixir/llm.txt" << 'EOF'
Elixir Installation (prebuilt binaries)
=======================================

This installation uses a lightweight manager with a versions/ layout and a current symlink.

Installation Location:
- Elixir versions: LANG_BASE_DIR/elixir/versions/<ver>-otp-<otp>
- Current symlink: LANG_BASE_DIR/elixir/current -> versions/<ver>-otp-<otp>
- Binaries: BIN_DIR (shims to current/bin)
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
  elixir-version install 1.17.3      # Install Elixir 1.17.3
  elixir-version list                # List installed versions
  elixir-version use 1.17.3          # Switch to a specific version (sets current)
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
- Elixir should match the installed Erlang/OTP version
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
echo "   - Installation directory: $INSTALL_DIR"
echo "   - Binaries available in: $BIN_DIR"
echo "   - Version: $ELIXIR_VERSION (OTP $ERLANG_OTP_VERSION)"
echo "   - Documentation: $LANG_BASE_DIR/elixir/llm.txt"
echo ""
echo "Managing Elixir versions:"
echo "   elixir-version install <version>   - Install Elixir"
echo "   elixir-version list                - List installed versions"
echo "   elixir-version use <version>       - Switch to a version"
echo ""
echo "Note: Prefer versions compatible with your Erlang/OTP."