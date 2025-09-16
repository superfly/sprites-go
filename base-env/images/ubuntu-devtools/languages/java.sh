#!/bin/bash
set -e

echo "=========================================="
echo "Installing Java (direct Temurin download)..."
echo "=========================================="

# Configuration with argument support
BASE_DIR="${1:-/opt}"  # Default to /opt, can be overridden with first argument
LANG_BASE_DIR="$BASE_DIR/languages"
BIN_DIR="$BASE_DIR/bin"
ETC_DIR="$BASE_DIR/etc/profile.d"

# Java specific configuration
JAVA_VERSION="${JAVA_VERSION:-21}"  # Latest LTS version
JAVA_BASE_DIR="$LANG_BASE_DIR/java"

echo "Installing Java (Eclipse Temurin)..."
echo "Base directory: $BASE_DIR"
echo "Default version: $JAVA_VERSION"

# Create directories with proper permissions
echo "Creating directories..."
mkdir -p "$JAVA_BASE_DIR" "$BIN_DIR" "$ETC_DIR"
chown -R $(id -u):$(id -g) "$LANG_BASE_DIR/java" "$BIN_DIR"

# Architecture detection
ARCH=$(uname -m)
case $ARCH in
    x86_64|amd64)
        ARCH_NAME="x64"
        ;;
    aarch64|arm64)
        ARCH_NAME="aarch64"
        ;;
    *)
        echo "Unsupported architecture: $ARCH"
        exit 1
        ;;
esac

# Use Adoptium API to get the latest release
echo "Getting latest Temurin $JAVA_VERSION release info..."
API_URL="https://api.adoptium.net/v3/assets/latest/${JAVA_VERSION}/hotspot"
DOWNLOAD_URL=$(curl -s "$API_URL" | grep -o "https://github.com/adoptium/[^\"]*jdk_${ARCH_NAME}_linux_hotspot[^\"]*\.tar\.gz" | grep -v "static-libs" | head -1)

if [ -z "$DOWNLOAD_URL" ]; then
    echo "Failed to get download URL from API, trying direct URL..."
    # Fallback to a known working URL pattern
    DOWNLOAD_URL="https://github.com/adoptium/temurin${JAVA_VERSION}-binaries/releases/download/jdk-${JAVA_VERSION}.0.6%2B10/OpenJDK${JAVA_VERSION}U-jdk_${ARCH_NAME}_linux_hotspot_${JAVA_VERSION}.0.6_10.tar.gz"
fi

echo "Downloading from: $DOWNLOAD_URL"
curl -fsSL -o "/tmp/temurin-${JAVA_VERSION}.tar.gz" "$DOWNLOAD_URL" || {
    echo "Download failed. Please check the Java version and try again."
    exit 1
}

# Extract to version-specific directory
JAVA_VERSION_DIR="$JAVA_BASE_DIR/$JAVA_VERSION"
mkdir -p "$JAVA_VERSION_DIR"
echo "Extracting Java to $JAVA_VERSION_DIR..."
tar -xzf "/tmp/temurin-${JAVA_VERSION}.tar.gz" -C "$JAVA_VERSION_DIR" --strip-components=1
rm "/tmp/temurin-${JAVA_VERSION}.tar.gz"

# Create symlinks
ln -sf "$JAVA_VERSION_DIR" "$JAVA_BASE_DIR/default"

# Create symlinks in BIN_DIR
echo "Creating symlinks in $BIN_DIR..."
for binary in "$JAVA_VERSION_DIR/bin"/*; do
    if [ -f "$binary" ] && [ -x "$binary" ]; then
        binary_name=$(basename "$binary")
        ln -sf "$binary" "$BIN_DIR/$binary_name"
        echo "  Linked: $binary_name"
    fi
done


# Verify installation
echo ""
echo "Verifying Java installation..."
"$BIN_DIR/java" -version
"$BIN_DIR/javac" -version

# Test Java
echo ""
echo "Testing Java..."
echo 'public class Hello { public static void main(String[] args) { System.out.println("Hello from Java " + System.getProperty("java.version") + "!"); } }' > /tmp/Hello.java
"$BIN_DIR/javac" /tmp/Hello.java
"$BIN_DIR/java" -cp /tmp Hello
rm /tmp/Hello.java /tmp/Hello.class

# Create Java version manager helper script
echo ""
echo "Creating Java version helper script..."
tee $BIN_DIR/java-version > /dev/null << 'SCRIPT_EOF'
#!/bin/bash
# Helper script for Java version management

JAVA_BASE_DIR="REPLACE_JAVA_BASE_DIR"
BIN_DIR="REPLACE_BIN_DIR"

# Architecture detection
ARCH=$(uname -m)
case $ARCH in
    x86_64|amd64)
        ARCH_NAME="x64"
        ;;
    aarch64|arm64)
        ARCH_NAME="aarch64"
        ;;
    *)
        echo "Unsupported architecture: $ARCH"
        exit 1
        ;;
esac

install_java() {
    version="$1"
    if [ -z "$version" ]; then
        echo "Error: Version required"
        echo "Usage: java-version install <version>"
        echo "Example: java-version install 17"
        return 1
    fi
    
    echo "Installing Java $version (Temurin)..."
    
    # Check if already installed
    if [ -d "$JAVA_BASE_DIR/$version" ]; then
        echo "Java $version is already installed"
        return 0
    fi
    
    # Use Adoptium API
    API_URL="https://api.adoptium.net/v3/assets/latest/${version}/hotspot"
    DOWNLOAD_URL=$(curl -s "$API_URL" | grep -o "https://github.com/adoptium/[^\"]*jdk_${ARCH_NAME}_linux_hotspot[^\"]*\.tar\.gz" | grep -v "static-libs" | head -1)
    
    if [ -z "$DOWNLOAD_URL" ]; then
        echo "Error: Could not find download URL for Java $version"
        return 1
    fi
    
    echo "Downloading from: $DOWNLOAD_URL"
    curl -fsSL -o "/tmp/temurin-${version}.tar.gz" "$DOWNLOAD_URL" || {
        echo "Download failed"
        return 1
    }
    
    # Extract to version-specific directory
    JAVA_VERSION_DIR="$JAVA_BASE_DIR/$version"
    mkdir -p "$JAVA_VERSION_DIR"
    tar -xzf "/tmp/temurin-${version}.tar.gz" -C "$JAVA_VERSION_DIR" --strip-components=1
    rm "/tmp/temurin-${version}.tar.gz"
    
    echo "Java $version installed"
    echo "To use: java-version use $version"
}

case "$1" in
    install)
        shift
        install_java "$@"
        ;;
    list)
        echo "Installed Java versions:"
        for dir in "$JAVA_BASE_DIR"/*; do
            if [ -d "$dir" ] && [ -f "$dir/bin/java" ]; then
                version=$(basename "$dir")
                if [ "$version" != "default" ]; then
                    # Check if this is the current version
                    if [ -L "$BIN_DIR/java" ]; then
                        current_target=$(readlink -f "$BIN_DIR/java")
                        if [[ "$current_target" == "$dir"* ]]; then
                            echo "  * $version (Temurin)"
                        else
                            echo "    $version (Temurin)"
                        fi
                    else
                        echo "    $version (Temurin)"
                    fi
                fi
            fi
        done
        ;;
    use)
        version="$2"
        if [ -z "$version" ]; then
            echo "Usage: java-version use <version>"
            echo "Example: java-version use 17"
            echo ""
            echo "This will update the symlinks in $BIN_DIR"
            exit 1
        fi
        
        # Check if version is installed
        if [ ! -d "$JAVA_BASE_DIR/$version" ]; then
            echo "Error: Java $version is not installed"
            echo "Run: java-version install $version"
            exit 1
        fi
        
        # Update symlinks
        echo "Switching to Java $version..."
        for binary in "$JAVA_BASE_DIR/$version/bin"/*; do
            if [ -f "$binary" ] && [ -x "$binary" ]; then
                binary_name=$(basename "$binary")
                ln -sf "$binary" "$BIN_DIR/$binary_name"
            fi
        done
        
        # Update default symlink
        ln -sf "$JAVA_BASE_DIR/$version" "$JAVA_BASE_DIR/default"
        
        echo "Java $version is now active"
        "$BIN_DIR/java" -version
        ;;
    current)
        if [ -L "$BIN_DIR/java" ]; then
            "$BIN_DIR/java" -version
        else
            echo "No Java version currently set"
        fi
        ;;
    *)
        echo "Java version manager helper"
        echo ""
        echo "Usage: java-version <command> [args]"
        echo ""
        echo "Commands:"
        echo "  install <version>  Install a Java version (8, 11, 17, 21)"
        echo "  list              List installed versions"
        echo "  use <version>     Switch to a specific version"
        echo "  current           Show current version"
        echo ""
        echo "Examples:"
        echo "  java-version install 17"
        echo "  java-version list"
        echo "  java-version use 17"
        echo ""
        echo "Note: Downloads Eclipse Temurin (OpenJDK) directly from Adoptium"
        echo "      Available LTS versions: 8, 11, 17, 21"
        ;;
esac
SCRIPT_EOF

# Replace placeholders in the helper script
sed -i "s|REPLACE_JAVA_BASE_DIR|$JAVA_BASE_DIR|g" $BIN_DIR/java-version
sed -i "s|REPLACE_BIN_DIR|$BIN_DIR|g" $BIN_DIR/java-version
chmod +x $BIN_DIR/java-version

# Create profile script
echo ""
echo "Creating Java environment configuration..."
tee $ETC_DIR/java.sh > /dev/null << EOF
# Java environment configuration
export JAVA_HOME="$JAVA_BASE_DIR/default"
export MAVEN_HOME="$LANG_BASE_DIR/java/.m2"
export GRADLE_USER_HOME="$LANG_BASE_DIR/java/.gradle"
# PATH should already include $BIN_DIR from elsewhere
EOF

# Create documentation
echo ""
echo "Creating Java documentation..."
cat > "$JAVA_BASE_DIR/llm.txt" << 'EOF'
Java Installation (Eclipse Temurin)
===================================

This is a direct installation of Eclipse Temurin (OpenJDK).

Installation Location:
- Java SDKs: LANG_BASE_DIR/java/<version>
- Default: LANG_BASE_DIR/java/default (symlink)
- Binaries: BIN_DIR (symlinked)

Default Version: JAVA_VERSION

Using Java:
-----------
Java is immediately available:
  java --version
  javac --version
  jar --version
  jshell

Building and Running:
---------------------
  javac MyClass.java          # Compile
  java MyClass                # Run
  jar cf myapp.jar *.class    # Create JAR
  java -jar myapp.jar         # Run JAR

Managing Versions:
------------------
Use the java-version helper script:
  java-version install 17     # Install Java 17
  java-version list           # List installed versions
  java-version use 17         # Switch to Java 17
  java-version current        # Show current version

Build Tools:
------------
Maven (install separately):
  curl -fsSL https://dlcdn.apache.org/maven/maven-3/3.9.6/binaries/apache-maven-3.9.6-bin.tar.gz | tar -xz
  # Add to PATH: export PATH=$PATH:/path/to/maven/bin

Gradle (install separately):
  curl -fsSL https://services.gradle.org/distributions/gradle-8.5-bin.zip -o gradle.zip
  unzip gradle.zip
  # Add to PATH: export PATH=$PATH:/path/to/gradle/bin

Using SDKMAN (alternative for tools):
  curl -s "https://get.sdkman.io" | bash
  sdk install maven
  sdk install gradle

Common Commands:
----------------
java --version              # Check Java version
javac MyClass.java          # Compile Java file
java MyClass                # Run compiled class
jshell                      # Interactive Java shell
jdb                         # Java debugger
jar tf myapp.jar            # List JAR contents
javap MyClass               # Disassemble class

Environment Variables:
----------------------
JAVA_HOME                   # Java installation directory
CLASSPATH                   # Java class search path
MAVEN_HOME                  # Maven installation
GRADLE_USER_HOME            # Gradle cache location
_JAVA_OPTIONS               # Default JVM options

Notes:
------
- Eclipse Temurin is the OpenJDK distribution from Adoptium
- LTS versions available: 8, 11, 17, 21
- Each version is installed in its own directory
- The 'default' symlink points to the active version
- Use java-version helper to manage multiple versions
- Build tools (Maven, Gradle) should be installed separately
EOF

# Replace placeholders in documentation
sed -i "s|LANG_BASE_DIR|$LANG_BASE_DIR|g" "$JAVA_BASE_DIR/llm.txt"
sed -i "s|BIN_DIR|$BIN_DIR|g" "$JAVA_BASE_DIR/llm.txt"
sed -i "s|JAVA_VERSION|$JAVA_VERSION|g" "$JAVA_BASE_DIR/llm.txt"

echo ""
echo "✅ Java $JAVA_VERSION installed successfully!"
echo "   - Installation directory: $JAVA_VERSION_DIR"
echo "   - Symlinked to: $JAVA_BASE_DIR/default"
echo "   - Binaries available in: $BIN_DIR"
echo "   - Default version: $JAVA_VERSION"
echo "   - Documentation: $JAVA_BASE_DIR/llm.txt"
echo ""
echo "Managing Java versions:"
echo "   java-version install <version>  - Install a Java version"
echo "   java-version list              - List installed versions"
echo "   java-version use <version>     - Switch to a version"
echo "   java-version current           - Show current version"
echo ""
echo "Examples:"
echo "   java-version install 17"
echo "   java-version use 17"
echo ""
echo "Available LTS versions: 8, 11, 17, 21"
echo "Note: Downloads Eclipse Temurin (OpenJDK) directly from Adoptium"