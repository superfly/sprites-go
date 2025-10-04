#!/bin/bash
set -e

# Implementation notes:
# See ./llm.txt in this directory for the filesystem layout and shim standard
# that other languages should follow (manager-first install, nvm-style shims).
# conforms to llm.txt and matches node layout

echo "=========================================="
echo "Installing Java (SDKMAN manager-first layout)..."
echo "=========================================="

# Configuration with argument support
BASE_DIR="${1:-/opt}"  # Default to /opt, can be overridden with first argument
LANG_BASE_DIR="$BASE_DIR/languages"
BIN_DIR="$BASE_DIR/bin"
ETC_DIR="$BASE_DIR/etc/profile.d" # reserved; no profile edits per llm.txt

# Java via SDKMAN configuration
JAVA_VERSION="${JAVA_VERSION:-25-tem}"
SDKMAN_DIR="$LANG_BASE_DIR/java/sdkman"

echo "Installing SDKMAN and Java..."
echo "Base directory: $BASE_DIR"
echo "Default Java version: $JAVA_VERSION"

# Create directories with proper permissions
echo "Creating directories..."
mkdir -p "$BIN_DIR" "$ETC_DIR"
chown -R $(id -u):$(id -g) "$BIN_DIR"

# Install SDKMAN (non-interactive)
# We set SDKMAN_DIR so the installer uses our manager-first layout
echo "Ensuring SDKMAN is installed..."
if [ ! -s "$SDKMAN_DIR/bin/sdkman-init.sh" ]; then
  rm -rf "$SDKMAN_DIR"
  export SDKMAN_DIR="$SDKMAN_DIR"
  export SDKMAN_CANDIDATES_DIR="$SDKMAN_DIR/candidates"
  curl -fsSL "https://get.sdkman.io" | bash
fi

# Source SDKMAN to use it
[ -s "$SDKMAN_DIR/bin/sdkman-init.sh" ] && \. "$SDKMAN_DIR/bin/sdkman-init.sh"

# Install default Java and set as default
echo "Installing Java $JAVA_VERSION via SDKMAN..."
# Invoke in a clean bash subshell that sources SDKMAN to ensure the sdk function is available
bash -lc "export SDKMAN_DIR='$SDKMAN_DIR'; \
  [ -s '$SDKMAN_DIR/bin/sdkman-init.sh' ] && source '$SDKMAN_DIR/bin/sdkman-init.sh'; \
  sdk install java '$JAVA_VERSION' <<< 'y'; \
  sdk default java '$JAVA_VERSION' || true"

# Create SDKMAN-enabled shims in BIN_DIR for core Java commands
# Shims follow llm.txt guidance: set env only if unset, source init, do not clean PATH
# and exec absolute binaries from the resolved bin dir.
echo "Creating SDKMAN-enabled shims in $BIN_DIR..."
for cmd in java javac jar jshell javadoc jcmd jstack jmap jps jstat keytool jlink jdeps; do
    cat > "$BIN_DIR/$cmd" << 'WRAP_EOF'
#!/bin/bash
set -e

DEFAULT_SDKMAN_DIR="REPLACE_SDKMAN_DIR"

# Only set SDKMAN_DIR if not already set
export SDKMAN_DIR="${SDKMAN_DIR:-$DEFAULT_SDKMAN_DIR}"
[ -s "$SDKMAN_DIR/bin/sdkman-init.sh" ] && . "$SDKMAN_DIR/bin/sdkman-init.sh"

# Resolve the Java binary directory for the active/default toolchain
JAVA_BIN_DIR="$SDKMAN_DIR/candidates/java/current/bin"
if [ ! -d "$JAVA_BIN_DIR" ]; then
  JAVA_BIN="$(command -v java || true)"
  JAVA_BIN_DIR="$(dirname "$JAVA_BIN")"
fi

# Add JAVA_BIN_DIR to PATH only if not already present
case ":$PATH:" in
  *":$JAVA_BIN_DIR:") ;;
  *) PATH="$JAVA_BIN_DIR:$PATH" ;;
esac

cmd_name="$(basename "$0")"
exec "$JAVA_BIN_DIR/$cmd_name" "$@"
WRAP_EOF
    sed -i "s|REPLACE_SDKMAN_DIR|$SDKMAN_DIR|g" "$BIN_DIR/$cmd"
    chmod +x "$BIN_DIR/$cmd"
    echo "  Created shim: $cmd"
done

# Verify installation via shims
echo ""
echo "Verifying Java installation..."
"$BIN_DIR/java" -version || true
"$BIN_DIR/javac" -version || true

# Skip compile/run in build stage; runtime tests handled by test-languages.sh

# Cleanup SDKMAN archives and tmp to reduce image size
echo "Cleaning Java/SDKMAN caches..."
rm -rf "$SDKMAN_DIR/archives" "$SDKMAN_DIR/tmp" 2>/dev/null || true

echo ""
echo "Java $JAVA_VERSION installed via SDKMAN"