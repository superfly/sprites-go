#!/bin/bash
set -e

echo "=========================================="
echo "Installing Rust (canonical rustup approach)..."
echo "=========================================="

# Configuration with argument support
BASE_DIR="${1:-/opt}"  # Default to /opt, can be overridden with first argument
LANG_BASE_DIR="$BASE_DIR/languages"
BIN_DIR="$BASE_DIR/bin"
ETC_DIR="$BASE_DIR/etc/profile.d"

# Rust specific configuration
RUST_VERSION="${RUST_VERSION:-1.89.0}"
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

# Source cargo env
source "$CARGO_HOME/env"

# Install the specified Rust version
echo "Installing Rust ${RUST_VERSION}..."
rustup toolchain install "$RUST_VERSION"
rustup default "$RUST_VERSION"

# Install common Rust components
echo "Installing Rust components..."
rustup component add clippy rust-src rust-analysis rustfmt

# Create symlinks
echo "Creating symlinks in $BIN_DIR..."
for binary in "$CARGO_HOME/bin"/*; do
    if [ -f "$binary" ] && [ -x "$binary" ]; then
        binary_name=$(basename "$binary")
        ln -sf "$binary" "$BIN_DIR/$binary_name"
        echo "  Linked: $binary_name"
    fi
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
rustup toolchain list

# Test Rust
echo ""
echo "Testing Rust..."
echo 'fn main() { println!("Hello from Rust!"); }' > /tmp/hello.rs
"$BIN_DIR/rustc" /tmp/hello.rs -o /tmp/hello
/tmp/hello
rm /tmp/hello.rs /tmp/hello

# Create a simple rust helper script
echo ""
echo "Creating rust helper script..."
tee $BIN_DIR/rust-toolchain > /dev/null << 'SCRIPT_EOF'
#!/bin/bash
# Helper script for Rust toolchain operations

RUSTUP_HOME="REPLACE_RUSTUP_HOME"
CARGO_HOME="REPLACE_CARGO_HOME"

export RUSTUP_HOME="$RUSTUP_HOME"
export CARGO_HOME="$CARGO_HOME"
export PATH="$CARGO_HOME/bin:$PATH"

case "$1" in
    install)
        version="$2"
        if [ -z "$version" ]; then
            echo "Usage: rust-toolchain install <version>"
            echo "Example: rust-toolchain install stable"
            echo "Example: rust-toolchain install 1.88.0"
            echo "Example: rust-toolchain install nightly"
            exit 1
        fi
        rustup toolchain install "$version"
        ;;
    list)
        rustup toolchain list
        ;;
    default)
        version="$2"
        if [ -z "$version" ]; then
            echo "Usage: rust-toolchain default <version>"
            echo "Example: rust-toolchain default 1.88.0"
            exit 1
        fi
        rustup default "$version"
        echo "Default toolchain set to $version"
        ;;
    *)
        echo "Rust toolchain helper"
        echo ""
        echo "Usage: rust-toolchain <command> [args]"
        echo ""
        echo "Commands:"
        echo "  install <version>  - Install a toolchain (stable, nightly, 1.88.0)"
        echo "  list              - List installed toolchains"
        echo "  default <version> - Set default toolchain"
        echo ""
        echo "Note: This is a wrapper around rustup commands"
        ;;
esac
SCRIPT_EOF

# Replace placeholders in the helper script
sed -i "s|REPLACE_RUSTUP_HOME|$RUSTUP_HOME|g" $BIN_DIR/rust-toolchain
sed -i "s|REPLACE_CARGO_HOME|$CARGO_HOME|g" $BIN_DIR/rust-toolchain
chmod +x $BIN_DIR/rust-toolchain

# Create profile script
echo ""
echo "Creating Rust environment configuration..."
tee $ETC_DIR/rust.sh > /dev/null << EOF
# Rust environment setup
export RUSTUP_HOME="$RUSTUP_HOME"
export CARGO_HOME="$CARGO_HOME"
source "\$CARGO_HOME/env"
# PATH should already include $BIN_DIR from elsewhere
EOF

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
- Binaries: BIN_DIR (symlinked)

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

Using helper script:
  rust-toolchain install stable
  rust-toolchain list
  rust-toolchain default 1.88.0

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
echo ""
echo "Helper commands:"
echo "   rust-toolchain install stable      - Wrapper for rustup toolchain install"
echo "   rust-toolchain list                - Wrapper for rustup toolchain list"
echo ""
echo "Examples:"
echo "   rustup toolchain install nightly"
echo "   rustup override set 1.88.0"
echo "   cargo +nightly test"