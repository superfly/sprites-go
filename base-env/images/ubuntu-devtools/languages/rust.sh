#!/bin/bash
set -e

# Implementation notes:
# See ./llm.txt in this directory for the filesystem layout and shim standard
# that other languages should follow (manager-first install, nvm-style shims).
# conforms to llm.txt and matches node layout

echo "=========================================="
echo "Installing Rust (canonical rustup approach)..."
echo "=========================================="

# Configuration with argument support
BASE_DIR="${1:-/opt}"  # Default to /opt, can be overridden with first argument
LANG_BASE_DIR="$BASE_DIR/languages"
BIN_DIR="$BASE_DIR/bin"
ETC_DIR="$BASE_DIR/etc/profile.d"

# Rust specific configuration
# Baseline pinned version as of 2025-10-04: 1.90.0
RUST_VERSION="${RUST_VERSION:-1.90.0}"
RUSTUP_HOME="$LANG_BASE_DIR/rust/rustup"
CARGO_HOME="$LANG_BASE_DIR/rust/cargo"

echo "Installing Rust with rustup..."
echo "Base directory: $BASE_DIR"
echo "Default version: $RUST_VERSION"

# Create directories with proper permissions
echo "Creating directories..."
mkdir -p "$RUSTUP_HOME" "$CARGO_HOME" "$BIN_DIR" "$ETC_DIR"
chown -R $(id -u):$(id -g) "$LANG_BASE_DIR/rust" "$BIN_DIR"

# Install rustup
echo "Downloading and installing rustup..."
export RUSTUP_HOME="$RUSTUP_HOME"
export CARGO_HOME="$CARGO_HOME"
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --no-modify-path --default-toolchain none

# Install the specified Rust version using explicit rustup path
RUSTUP_BIN="$CARGO_HOME/bin/rustup"
echo "Installing Rust ${RUST_VERSION}..."
"$RUSTUP_BIN" toolchain install "$RUST_VERSION"
"$RUSTUP_BIN" default "$RUST_VERSION"

# Install common Rust components
echo "Installing Rust components..."
"$RUSTUP_BIN" component add clippy rust-src rust-analysis rustfmt

# Create wrapper shims in BIN_DIR for core Rust commands
echo "Creating rustup-enabled shims in $BIN_DIR..."
for cmd in rustc cargo rustup rustfmt rustdoc; do
    cat > "$BIN_DIR/$cmd" << 'WRAP_EOF'
#!/bin/bash
set -e

# rustup-enabled shim that ensures active Rust toolchain is available
DEFAULT_RUSTUP_HOME="REPLACE_RUSTUP_HOME"
DEFAULT_CARGO_HOME="REPLACE_CARGO_HOME"

# Only set manager env vars if not already set
export RUSTUP_HOME="${RUSTUP_HOME:-$DEFAULT_RUSTUP_HOME}"
export CARGO_HOME="${CARGO_HOME:-$DEFAULT_CARGO_HOME}"

# Resolve the Rust binary directory (proxies live in CARGO_HOME/bin)
RUST_BIN_DIR="$CARGO_HOME/bin"

# Add RUST_BIN_DIR to PATH only if not already present
case ":$PATH:" in
  *":$RUST_BIN_DIR:") ;;
  *) export PATH="$RUST_BIN_DIR:$PATH" ;;
esac

cmd_name="$(basename "$0")"
exec "$RUST_BIN_DIR/$cmd_name" "$@"
WRAP_EOF
    sed -i "s|REPLACE_RUSTUP_HOME|$RUSTUP_HOME|g" "$BIN_DIR/$cmd"
    sed -i "s|REPLACE_CARGO_HOME|$CARGO_HOME|g" "$BIN_DIR/$cmd"
    chmod +x "$BIN_DIR/$cmd"
    echo "  Created shim: $cmd"
done


# Verify installation
echo ""
echo "Verifying Rust installation..."
"$BIN_DIR/rustc" --version
"$BIN_DIR/cargo" --version
"$BIN_DIR/rustup" --version

# Show installed toolchains
echo ""
echo "Installed toolchains:"
"$RUSTUP_BIN" toolchain list

# Test Rust
echo ""
echo "Testing Rust..."
echo 'fn main() { println!("Hello from Rust!"); }' > /tmp/hello.rs
"$BIN_DIR/rustc" /tmp/hello.rs -o /tmp/hello
/tmp/hello
rm /tmp/hello.rs /tmp/hello

# Cleanup cargo/rustup download caches
echo "Cleaning Rust caches..."
"$RUSTUP_BIN" self update -y >/dev/null 2>&1 || true
rm -rf "$CARGO_HOME/registry/index" "$CARGO_HOME/registry/cache" "$CARGO_HOME/git/db" "$RUSTUP_HOME/downloads" "$RUSTUP_HOME/tmp" 2>/dev/null || true

## No helper script; rustup proxies are invoked via shims
## No profile script; shims ensure PATH dynamically

# Create documentation
echo ""
echo "Creating Rust documentation..."
cat > "$LANG_BASE_DIR/rust/llm.txt" << 'EOF'
Rust Installation (via rustup)
==============================

This installation uses rustup for managing Rust toolchains.

Installation Location:
- rustup: LANG_BASE_DIR/rust/rustup
- cargo: LANG_BASE_DIR/rust/cargo
- Binaries: BIN_DIR (shim wrappers)

Default Version: RUST_VERSION

Using Rust:
-----------
Rust is immediately available:
  rustc --version
  cargo --version
  cargo new my_project
  cargo build
  cargo run
  cargo test

Managing Toolchains:
--------------------
Using rustup directly:
  rustup toolchain install stable     # Install stable
  rustup toolchain install nightly    # Install nightly
  rustup toolchain install 1.88.0     # Install specific version
  rustup toolchain list               # List toolchains
  rustup default stable               # Set default
  rustup override set nightly         # Set for current directory
  rustup update                       # Update toolchains

Installing Crates:
------------------
Global tools (installed to CARGO_HOME/bin):
  cargo install ripgrep
  cargo install cargo-edit
  cargo install sccache

Project dependencies (in Cargo.toml):
  [dependencies]
  serde = "1.0"
  tokio = { version = "1.0", features = ["full"] }

Using Different Toolchains:
---------------------------
For a single command:
  cargo +nightly build
  cargo +1.88.0 test
  rustc +stable --version

Common Commands:
----------------
cargo new my_project        # Create new project
cargo init                  # Initialize in existing directory
cargo build                 # Build project
cargo build --release       # Build optimized
cargo run                   # Build and run
cargo test                  # Run tests
cargo doc --open            # Generate and open docs
cargo clippy                # Run linter
cargo fmt                   # Format code
cargo clean                 # Clean build artifacts

Environment Variables:
----------------------
RUSTUP_HOME                 # rustup installation
CARGO_HOME                  # cargo and installed tools
RUST_BACKTRACE             # Set to 1 for full backtraces
CARGO_TARGET_DIR           # Override build directory

Notes:
------
- Components included: clippy, rust-src, rust-analysis, rustfmt
- Use rust-toolchain.toml in projects to specify toolchain
- cargo install puts binaries in CARGO_HOME/bin
- Each project has its own target/ directory for builds
- Use cargo workspaces for multi-crate projects
- Shims dynamically set PATH; no shell profile scripts are modified
EOF

# Replace placeholders in documentation
sed -i "s|LANG_BASE_DIR|$LANG_BASE_DIR|g" "$LANG_BASE_DIR/rust/llm.txt"
sed -i "s|BIN_DIR|$BIN_DIR|g" "$LANG_BASE_DIR/rust/llm.txt"
sed -i "s|RUST_VERSION|$RUST_VERSION|g" "$LANG_BASE_DIR/rust/llm.txt"

echo ""
echo "✅ Rust $RUST_VERSION installed successfully!"
echo "   - Installation directory: $LANG_BASE_DIR/rust"
echo "   - Binaries available in: $BIN_DIR"
echo "   - Default toolchain: $RUST_VERSION"
echo "   - Documentation: $LANG_BASE_DIR/rust/llm.txt"
echo ""
echo "Managing Rust versions (canonical rustup way):"
echo "   rustup toolchain install <version>  - Install a toolchain (1.90.0, stable, nightly)"
echo "   rustup toolchain list              - List installed toolchains"
echo "   rustup default <version>           - Set global default"
echo "   rustup override set <version>      - Set version for current directory"
echo "   cargo +<version> <command>         - Use version for one command"