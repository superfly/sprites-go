#!/bin/bash
set -e

echo "=========================================="
echo "Installing Go (direct download)..."
echo "=========================================="

# Configuration with argument support
BASE_DIR="${1:-/opt}"  # Default to /opt, can be overridden with first argument
LANG_BASE_DIR="$BASE_DIR/languages"
BIN_DIR="$BASE_DIR/bin"
ETC_DIR="$BASE_DIR/etc/profile.d"

# Go specific configuration
GO_VERSION="${GO_VERSION:-1.23.4}"
GO_BASE_DIR="$LANG_BASE_DIR/go"

echo "Installing Go..."
echo "Base directory: $BASE_DIR"
echo "Default version: $GO_VERSION"

# Create directories with proper permissions
echo "Creating directories..."
mkdir -p "$GO_BASE_DIR" "$BIN_DIR" "$ETC_DIR"
chown -R $(id -u):$(id -g) "$LANG_BASE_DIR/go" "$BIN_DIR"

# Architecture detection
ARCH=$(uname -m)
case $ARCH in
    x86_64|amd64)
        ARCH_NAME="amd64"
        ;;
    aarch64|arm64)
        ARCH_NAME="arm64"
        ;;
    *)
        echo "Unsupported architecture: $ARCH"
        exit 1
        ;;
esac

# Download and install Go
DOWNLOAD_URL="https://go.dev/dl/go${GO_VERSION}.linux-${ARCH_NAME}.tar.gz"
echo "Downloading Go ${GO_VERSION} from: $DOWNLOAD_URL"
curl -fsSL -o "/tmp/go${GO_VERSION}.tar.gz" "$DOWNLOAD_URL"

# Extract to version-specific directory
GO_VERSION_DIR="$GO_BASE_DIR/versions/$GO_VERSION"
mkdir -p "$GO_VERSION_DIR"
echo "Extracting Go to $GO_VERSION_DIR..."
tar -xzf "/tmp/go${GO_VERSION}.tar.gz" -C "$GO_VERSION_DIR" --strip-components=1
rm "/tmp/go${GO_VERSION}.tar.gz"

# Create symlink for current version
ln -sf "$GO_VERSION_DIR" "$GO_BASE_DIR/current"

# Create symlinks in BIN_DIR
echo "Creating symlinks in $BIN_DIR..."
for binary in "$GO_VERSION_DIR/bin"/*; do
    if [ -f "$binary" ] && [ -x "$binary" ]; then
        binary_name=$(basename "$binary")
        ln -sf "$binary" "$BIN_DIR/$binary_name"
        echo "  Linked: $binary_name"
    fi
done

# Create workspace directory
GOPATH="$GO_BASE_DIR/workspace"
mkdir -p "$GOPATH/src" "$GOPATH/bin" "$GOPATH/pkg"


# Verify installation
echo ""
echo "Verifying Go installation..."
"$BIN_DIR/go" version

# Test Go
echo ""
echo "Testing Go..."
cat > /tmp/hello.go << 'EOF'
package main
import (
    "fmt"
    "runtime"
)
func main() {
    fmt.Printf("Hello from Go %s!\n", runtime.Version())
}
EOF
"$BIN_DIR/go" run /tmp/hello.go
rm /tmp/hello.go

# Create Go version manager script
echo ""
echo "Creating Go version helper script..."
tee $BIN_DIR/go-version > /dev/null << 'SCRIPT_EOF'
#!/bin/bash
# Helper script for Go version management

GO_BASE_DIR="REPLACE_GO_BASE_DIR"
BIN_DIR="REPLACE_BIN_DIR"

# Architecture detection
ARCH=$(uname -m)
case $ARCH in
    x86_64|amd64)
        ARCH_NAME="amd64"
        ;;
    aarch64|arm64)
        ARCH_NAME="arm64"
        ;;
    *)
        echo "Unsupported architecture: $ARCH"
        exit 1
        ;;
esac

install_go() {
    version="$1"
    if [ -z "$version" ]; then
        echo "Error: Version required"
        echo "Usage: go-version install <version>"
        echo "Example: go-version install 1.22.0"
        return 1
    fi
    
    echo "Installing Go $version..."
    
    # Check if already installed
    if [ -d "$GO_BASE_DIR/versions/$version" ]; then
        echo "Go $version is already installed"
        return 0
    fi
    
    DOWNLOAD_URL="https://go.dev/dl/go${version}.linux-${ARCH_NAME}.tar.gz"
    echo "Downloading from: $DOWNLOAD_URL"
    curl -fsSL -o "/tmp/go${version}.tar.gz" "$DOWNLOAD_URL" || {
        echo "Download failed. Please check the version number."
        return 1
    }
    
    # Extract to version-specific directory
    GO_VERSION_DIR="$GO_BASE_DIR/versions/$version"
    mkdir -p "$GO_VERSION_DIR"
    tar -xzf "/tmp/go${version}.tar.gz" -C "$GO_VERSION_DIR" --strip-components=1
    rm "/tmp/go${version}.tar.gz"
    
    echo "Go $version installed"
    echo "To use: go-version use $version"
}

case "$1" in
    install)
        shift
        install_go "$@"
        ;;
    list)
        echo "Installed Go versions:"
        for dir in "$GO_BASE_DIR/versions"/*/; do
            if [ -d "$dir" ]; then
                version=$(basename "$dir")
                # Check if this is the current version
                if [ -L "$GO_BASE_DIR/current" ]; then
                    current_target=$(readlink -f "$GO_BASE_DIR/current")
                    if [[ "$current_target" == "$(readlink -f "$dir")" ]]; then
                        echo "  * $version"
                    else
                        echo "    $version"
                    fi
                else
                    echo "    $version"
                fi
            fi
        done
        ;;
    use)
        version="$2"
        if [ -z "$version" ]; then
            echo "Usage: go-version use <version>"
            echo "Example: go-version use 1.22.0"
            exit 1
        fi
        
        # Check if version is installed
        if [ ! -d "$GO_BASE_DIR/versions/$version" ]; then
            echo "Error: Go $version is not installed"
            echo "Run: go-version install $version"
            exit 1
        fi
        
        # Update symlinks
        echo "Switching to Go $version..."
        ln -sf "$GO_BASE_DIR/versions/$version" "$GO_BASE_DIR/current"
        for binary in "$GO_BASE_DIR/versions/$version/bin"/*; do
            if [ -f "$binary" ] && [ -x "$binary" ]; then
                binary_name=$(basename "$binary")
                ln -sf "$binary" "$BIN_DIR/$binary_name"
            fi
        done
        
        echo "Go $version is now active"
        "$BIN_DIR/go" version
        ;;
    current)
        "$BIN_DIR/go" version
        ;;
    *)
        echo "Go version manager helper"
        echo ""
        echo "Usage: go-version <command> [args]"
        echo ""
        echo "Commands:"
        echo "  install <version>  Install a Go version"
        echo "  list              List installed versions"
        echo "  use <version>     Switch to a specific version"
        echo "  current           Show current version"
        echo ""
        echo "Examples:"
        echo "  go-version install 1.22.0"
        echo "  go-version list"
        echo "  go-version use 1.22.0"
        echo ""
        echo "Note: Downloads official Go releases directly from go.dev"
        ;;
esac
SCRIPT_EOF

# Replace placeholders in the helper script
sed -i "s|REPLACE_GO_BASE_DIR|$GO_BASE_DIR|g" $BIN_DIR/go-version
sed -i "s|REPLACE_BIN_DIR|$BIN_DIR|g" $BIN_DIR/go-version
chmod +x $BIN_DIR/go-version

# Create profile script
echo ""
echo "Creating Go environment configuration..."
tee $ETC_DIR/go.sh > /dev/null << EOF
# Go environment configuration
export GOROOT="$GO_BASE_DIR/current"
export GOPATH="$GO_BASE_DIR/workspace"
export GOCACHE="$GO_BASE_DIR/.cache/go-build"
export GOMODCACHE="$GO_BASE_DIR/.cache/mod"
export PATH="\$GOPATH/bin:\$PATH"
# PATH should already include $BIN_DIR from elsewhere
EOF

# Create documentation
echo ""
echo "Creating Go documentation..."
cat > "$GO_BASE_DIR/llm.txt" << 'EOF'
Go Installation (Direct Download)
=================================

This is a direct installation of official Go releases.

Installation Location:
- Go versions: LANG_BASE_DIR/go/versions/<version>
- Current version: LANG_BASE_DIR/go/current (symlink)
- Binaries: BIN_DIR (symlinked)
- Workspace: LANG_BASE_DIR/go/workspace (GOPATH)

Default Version: GO_VERSION

Using Go:
---------
Go is immediately available:
  go version
  go build
  go run main.go
  go test
  go mod init

Managing Versions:
------------------
Use the go-version helper script:
  go-version install 1.22.0    # Install a Go version
  go-version list              # List installed versions
  go-version use 1.22.0        # Switch to a version
  go-version current           # Show current version

Module Management:
------------------
  go mod init example.com/app  # Initialize module
  go get github.com/pkg/errors # Add dependency
  go mod download              # Download dependencies
  go mod tidy                  # Clean up go.mod
  go mod vendor                # Vendor dependencies

Installing Tools:
-----------------
Tools are installed to GOPATH/bin:
  go install github.com/golangci/golangci-lint/cmd/golangci-lint@latest
  go install golang.org/x/tools/gopls@latest
  go install github.com/go-delve/delve/cmd/dlv@latest

Building:
---------
  go build                     # Build current package
  go build -o myapp            # Build with custom output
  go build ./...               # Build all packages
  CGO_ENABLED=0 go build       # Static binary

Cross-compilation:
  GOOS=linux GOARCH=amd64 go build
  GOOS=windows GOARCH=amd64 go build
  GOOS=darwin GOARCH=arm64 go build

Common Commands:
----------------
go version                   # Check Go version
go env                       # Show environment
go list ./...                # List packages
go fmt ./...                 # Format code
go vet ./...                 # Check for errors
go test ./...                # Run tests
go test -v -cover ./...      # Verbose with coverage
go clean -cache              # Clear build cache

Environment Variables:
----------------------
GOROOT                       # Go installation directory
GOPATH                       # Workspace directory
GOCACHE                      # Build cache location
GOMODCACHE                   # Module cache location
GO111MODULE                  # Module mode (auto/on/off)
GOPROXY                      # Module proxy
CGO_ENABLED                  # Enable/disable cgo

Notes:
------
- Go modules are the standard dependency management
- Tools installed with 'go install' go to GOPATH/bin
- Each Go version is completely independent
- Use go-version helper to manage multiple versions
- Build cache significantly speeds up compilation
EOF

# Replace placeholders in documentation
sed -i "s|LANG_BASE_DIR|$LANG_BASE_DIR|g" "$GO_BASE_DIR/llm.txt"
sed -i "s|BIN_DIR|$BIN_DIR|g" "$GO_BASE_DIR/llm.txt"
sed -i "s|GO_VERSION|$GO_VERSION|g" "$GO_BASE_DIR/llm.txt"

echo ""
echo "✅ Go $GO_VERSION installed successfully!"
echo "   - Installation directory: $GO_BASE_DIR"
echo "   - Binaries available in: $BIN_DIR"
echo "   - Current version: $GO_VERSION"
echo "   - GOPATH: $GOPATH"
echo "   - Documentation: $GO_BASE_DIR/llm.txt"
echo ""
echo "Managing Go versions:"
echo "   go-version install <version>  - Install a Go version"
echo "   go-version list              - List installed versions"
echo "   go-version use <version>     - Switch to a version"
echo ""
echo "Examples:"
echo "   go-version install 1.22.0"
echo "   go-version use 1.22.0"
echo ""
echo "Available at: https://go.dev/dl/"