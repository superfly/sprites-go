#!/bin/bash
set -e

echo "=========================================="
echo "Installing Python (canonical pyenv approach)..."
echo "=========================================="

# Configuration with argument support
BASE_DIR="${1:-/opt}"  # Default to /opt, can be overridden with first argument
LANG_BASE_DIR="$BASE_DIR/languages"
BIN_DIR="$BASE_DIR/bin"
ETC_DIR="$BASE_DIR/etc/profile.d"

# Python specific configuration
PYTHON_VERSION="${PYTHON_VERSION:-3.12.4}"
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

# Setup pyenv environment
export PYENV_ROOT="$PYENV_ROOT"
export PATH="$PYENV_ROOT/bin:$PATH"
eval "$(pyenv init -)"

# Install Python
echo "Installing Python ${PYTHON_VERSION}..."
pyenv install "$PYTHON_VERSION"
pyenv global "$PYTHON_VERSION"

# Upgrade pip
echo "Upgrading pip..."
pip install --upgrade pip

# Install common Python tools
echo "Installing common Python tools..."
pip install setuptools wheel virtualenv pipenv poetry

# Create symlinks in BIN_DIR
echo "Creating symlinks in $BIN_DIR..."
# Symlink pyenv binary
ln -sf "$PYENV_ROOT/bin/pyenv" "$BIN_DIR/pyenv"
echo "  Linked: pyenv"

# Symlink Python binaries from shims
for binary in "$PYENV_ROOT/shims"/{python,python3,pip,pip3,pipenv,poetry,virtualenv}; do
    if [ -f "$binary" ] && [ -x "$binary" ]; then
        binary_name=$(basename "$binary")
        ln -sf "$binary" "$BIN_DIR/$binary_name"
        echo "  Linked: $binary_name"
    fi
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
pyenv versions

# Test Python
echo ""
echo "Testing Python..."
"$BIN_DIR/python" -c "import sys; print(f'Hello from Python {sys.version.split()[0]}!')"

# Create pyenv helper script
echo ""
echo "Creating pyenv helper script..."
tee $BIN_DIR/pyenv-helper > /dev/null << 'SCRIPT_EOF'
#!/bin/bash
# Helper script for pyenv operations

PYENV_ROOT="REPLACE_PYENV_ROOT"
BIN_DIR="REPLACE_BIN_DIR"

export PYENV_ROOT="$PYENV_ROOT"
export PATH="$PYENV_ROOT/bin:$PATH"
eval "$(pyenv init -)"

case "$1" in
    install)
        version="$2"
        if [ -z "$version" ]; then
            echo "Usage: pyenv-helper install <version>"
            echo "Example: pyenv-helper install 3.11.0"
            exit 1
        fi
        
        pyenv install "$version"
        echo "Python $version installed"
        echo "To use: pyenv-helper global $version"
        ;;
    list)
        pyenv versions
        ;;
    global)
        version="$2"
        if [ -z "$version" ]; then
            echo "Usage: pyenv-helper global <version>"
            echo "Example: pyenv-helper global 3.12.0"
            exit 1
        fi
        
        pyenv global "$version"
        
        # Update symlinks
        for binary in "$PYENV_ROOT/shims"/{python,python3,pip,pip3,pipenv,poetry,virtualenv}; do
            if [ -f "$binary" ] && [ -x "$binary" ]; then
                binary_name=$(basename "$binary")
                ln -sf "$binary" "$BIN_DIR/$binary_name"
            fi
        done
        
        echo "Python $version is now the global default"
        echo "Symlinks updated in $BIN_DIR"
        ;;
    local)
        version="$2"
        if [ -z "$version" ]; then
            echo "Usage: pyenv-helper local <version>"
            echo "Example: pyenv-helper local 3.11.0"
            echo ""
            echo "This sets the Python version for the current directory"
            exit 1
        fi
        
        pyenv local "$version"
        echo "Python $version set for current directory"
        ;;
    *)
        echo "Python version manager (pyenv) helper"
        echo ""
        echo "Usage: pyenv-helper <command> [args]"
        echo ""
        echo "Commands:"
        echo "  install <version>  - Install a Python version"
        echo "  list              - List installed versions"
        echo "  global <version>  - Set global Python version"
        echo "  local <version>   - Set local Python version for current directory"
        echo ""
        echo "Examples:"
        echo "  pyenv-helper install 3.11.0"
        echo "  pyenv-helper list"
        echo "  pyenv-helper global 3.12.0"
        ;;
esac
SCRIPT_EOF

# Replace placeholders in the helper script
sed -i "s|REPLACE_PYENV_ROOT|$PYENV_ROOT|g" $BIN_DIR/pyenv-helper
sed -i "s|REPLACE_BIN_DIR|$BIN_DIR|g" $BIN_DIR/pyenv-helper
chmod +x $BIN_DIR/pyenv-helper

# Create profile script
echo ""
echo "Creating Python/pyenv environment configuration..."
tee $ETC_DIR/pyenv.sh > /dev/null << EOF
# Python/pyenv environment setup
export PYENV_ROOT="$PYENV_ROOT"
export PATH="\$PYENV_ROOT/bin:\$PATH"
eval "\$(pyenv init -)"
eval "\$(pyenv virtualenv-init -)"
# Configure pip cache location
export PIP_CACHE_DIR="$LANG_BASE_DIR/python/.cache/pip"
# PATH should already include $BIN_DIR from elsewhere
EOF

# Create documentation
echo ""
echo "Creating Python documentation..."
cat > "$LANG_BASE_DIR/python/llm.txt" << 'EOF'
Python Installation (via pyenv)
===============================

This installation uses pyenv for managing Python versions.

Installation Location:
- pyenv: LANG_BASE_DIR/python/pyenv
- Binaries: BIN_DIR (symlinked from shims)
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
Option 1: Use the helper script (no sourcing required):
  pyenv-helper install 3.11.0  # Install a new version
  pyenv-helper list            # List installed versions
  pyenv-helper global 3.11.0   # Set global default
  pyenv-helper local 3.10.0    # Set version for current directory

Option 2: Use pyenv directly (requires environment setup):
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
- Binary symlinks in BIN_DIR always point to the global version
- The helper script updates symlinks when switching versions
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