#!/bin/bash
set -e

# Implementation notes:
# See ./llm.txt in this directory for the filesystem layout and shim standard
# that other languages should follow (manager-first install, nvm-style shims).
# conforms to llm.txt and matches node layout

echo "=========================================="
echo "Installing Python (canonical pyenv approach)..."
echo "=========================================="

# Configuration with argument support
BASE_DIR="${1:-/opt}"  # Default to /opt, can be overridden with first argument
LANG_BASE_DIR="$BASE_DIR/languages"
BIN_DIR="$BASE_DIR/bin"
ETC_DIR="$BASE_DIR/etc/profile.d"

# Python specific configuration
# Baseline pinned version as of 2025-10-04: 3.13.7
PYTHON_VERSION="${PYTHON_VERSION:-3.13.7}"
PYENV_ROOT="$LANG_BASE_DIR/python/pyenv"

echo "Installing pyenv and Python..."
echo "Base directory: $BASE_DIR"
echo "Default version: $PYTHON_VERSION"

# Note: Build dependencies should be installed in the base image:
# make build-essential libssl-dev zlib1g-dev libbz2-dev libreadline-dev
# libsqlite3-dev wget curl llvm libncursesw5-dev xz-utils tk-dev
# libxml2-dev libxmlsec1-dev libffi-dev liblzma-dev

# Create directories with proper permissions
echo "Creating directories..."
mkdir -p "$PYENV_ROOT" "$BIN_DIR" "$ETC_DIR"
chown -R $(id -u):$(id -g) "$LANG_BASE_DIR/python" "$BIN_DIR"

# Install pyenv
echo "Installing pyenv..."
git clone https://github.com/pyenv/pyenv.git "$PYENV_ROOT"
cd "$PYENV_ROOT" && src/configure && make -C src

# Install pyenv-virtualenv plugin
echo "Installing pyenv-virtualenv plugin..."
mkdir -p "$PYENV_ROOT/plugins"
git clone https://github.com/pyenv/pyenv-virtualenv.git "$PYENV_ROOT/plugins/pyenv-virtualenv"

# Remove .git directories to save space (readonly installation)
rm -rf "$PYENV_ROOT/.git"
rm -rf "$PYENV_ROOT/plugins/pyenv-virtualenv/.git"

# Setup pyenv environment (no shell eval)
export PYENV_ROOT="$PYENV_ROOT"
export PATH="$PYENV_ROOT/bin:$PATH"
PYENV_BIN="$PYENV_ROOT/bin/pyenv"

# Install Python using explicit pyenv binary
echo "Installing Python ${PYTHON_VERSION}..."
"$PYENV_BIN" install "$PYTHON_VERSION"
"$PYENV_BIN" global "$PYTHON_VERSION"
"$PYENV_BIN" rehash

# Upgrade pip via shim directly
echo "Upgrading pip..."
"$PYENV_ROOT/shims/pip" install --upgrade pip

# Install common Python tools
echo "Installing common Python tools..."
"$PYENV_ROOT/shims/pip" install setuptools wheel virtualenv pipenv poetry

# Cleanup pip and build caches to reduce image size
echo "Cleaning Python caches..."
"$PYENV_ROOT/shims/pip" cache purge || true
rm -rf "$PYENV_ROOT/sources" 2>/dev/null || true

# Create wrapper shims in BIN_DIR for core Python commands
echo "Creating pyenv-enabled shims in $BIN_DIR..."
for cmd in python python3 pip pip3 pipenv poetry virtualenv pyenv; do
    cat > "$BIN_DIR/$cmd" << 'WRAP_EOF'
#!/bin/bash
set -e

# pyenv-enabled shim that ensures active Python is available
DEFAULT_PYENV_ROOT="REPLACE_PYENV_ROOT"

export PYENV_ROOT="${PYENV_ROOT:-$DEFAULT_PYENV_ROOT}"

# Ensure pyenv bin and shims are on PATH
case ":$PATH:" in
  *":$PYENV_ROOT/bin:") ;;
  *) PATH="$PYENV_ROOT/bin:$PATH" ;;
esac
case ":$PATH:" in
  *":$PYENV_ROOT/shims:") ;;
  *) PATH="$PYENV_ROOT/shims:$PATH" ;;
esac

cmd_name="$(basename "$0")"
if [ "$cmd_name" = "pyenv" ]; then
  exec "$PYENV_ROOT/bin/pyenv" "$@"
else
  exec "$PYENV_ROOT/shims/$cmd_name" "$@"
fi
WRAP_EOF
    sed -i "s|REPLACE_PYENV_ROOT|$PYENV_ROOT|g" "$BIN_DIR/$cmd"
    chmod +x "$BIN_DIR/$cmd"
    echo "  Created shim: $cmd"
done


# Verify installation
echo ""
echo "Verifying Python installation..."
"$BIN_DIR/python" --version
"$BIN_DIR/pip" --version
"$BIN_DIR/pyenv" --version

# Show installed versions
echo ""
echo "Installed Python versions:"
"$PYENV_BIN" versions

# Test Python
echo ""
echo "Testing Python..."
"$BIN_DIR/python" -c "import sys; print(f'Hello from Python {sys.version.split()[0]}!')"

## No helper script; pyenv is invoked via shims
## No profile script; shims ensure PATH dynamically

# Create documentation
echo ""
echo "Creating Python documentation..."
cat > "$LANG_BASE_DIR/python/llm.txt" << 'EOF'
Python Installation (via pyenv)
===============================

This installation uses pyenv for managing Python versions.

Installation Location:
- pyenv: LANG_BASE_DIR/python/pyenv
- Binaries: BIN_DIR (shim wrappers)
- Packages: Within each Python version's site-packages

Default Version: PYTHON_VERSION

Using Python:
-------------
The default Python version is immediately available:
  python --version
  pip --version
  python -m venv myenv
  pipenv --version
  poetry --version

Managing Versions:
------------------
Use pyenv directly (shims handle PATH at runtime):
  pyenv install 3.11.0
  pyenv global 3.11.0
  pyenv local 3.10.0
  pyenv versions

Virtual Environments:
---------------------
Using venv (built-in):
  python -m venv myenv
  source myenv/bin/activate   # Linux/Mac
  myenv\Scripts\activate      # Windows
  deactivate

Using virtualenv:
  virtualenv myenv
  source myenv/bin/activate

Using pipenv:
  pipenv install              # Create Pipfile and virtualenv
  pipenv shell                # Activate shell
  pipenv install requests     # Add dependency

Using poetry:
  poetry new myproject        # Create new project
  poetry install              # Install dependencies
  poetry add requests         # Add dependency

Installing Packages:
--------------------
Global packages (for current Python version):
  pip install <package>

In virtual environments:
  pip install <package>       # After activation
  pipenv install <package>    # Using pipenv
  poetry add <package>        # Using poetry

Common Commands:
----------------
python --version            # Check Python version
pip list                    # List installed packages
pip freeze                  # List packages with versions
pyenv-helper list           # List installed Python versions
pyenv-helper install latest # Install latest stable Python

Environment Variables:
----------------------
PYENV_ROOT                  # pyenv installation directory
PYTHONPATH                  # Additional Python module directories
PIP_CACHE_DIR               # pip cache location
VIRTUAL_ENV                 # Current virtual environment

Notes:
------
- Each Python version has its own packages
- Use .python-version files in projects to specify Python version
- pyenv-virtualenv plugin is installed for virtual environment management
- Common tools pre-installed: setuptools, wheel, virtualenv, pipenv, poetry
- Shims dynamically set PATH; no shell profile scripts are modified
EOF

# Replace placeholders in documentation
sed -i "s|LANG_BASE_DIR|$LANG_BASE_DIR|g" "$LANG_BASE_DIR/python/llm.txt"
sed -i "s|BIN_DIR|$BIN_DIR|g" "$LANG_BASE_DIR/python/llm.txt"
sed -i "s|PYTHON_VERSION|$PYTHON_VERSION|g" "$LANG_BASE_DIR/python/llm.txt"

echo ""
echo "✅ Python $PYTHON_VERSION installed successfully with pyenv!"
echo "   - Installation directory: $PYENV_ROOT"
echo "   - Binaries available in: $BIN_DIR"
echo "   - Global version: $PYTHON_VERSION"
echo "   - Documentation: $LANG_BASE_DIR/python/llm.txt"
echo ""
echo "Managing Python versions (canonical pyenv way):"
echo "   pyenv install <version>    - Install a Python version"
echo "   pyenv versions            - List installed versions"
echo "   pyenv global <version>     - Set global default"
echo "   pyenv local <version>      - Set version for current directory"
echo ""
echo "Helper commands (works without sourcing pyenv):"
echo "   pyenv-helper install 3.11.0"
echo "   pyenv-helper list"
echo "   pyenv-helper global 3.12.0"
echo ""
echo "Note: To use pyenv commands in your shell, run:"
echo "   export PYENV_ROOT=\"$PYENV_ROOT\""
echo "   export PATH=\"\$PYENV_ROOT/bin:\$PATH\""
echo "   eval \"\$(pyenv init -)\""