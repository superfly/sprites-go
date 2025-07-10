.PHONY: build clean install test help

# Build the sprite-run binary
build:
	go build -o sprite-run .

# Clean build artifacts
clean:
	rm -f sprite-run

# Install the binary to local bin directory
install: build
	cp sprite-run $(HOME)/bin/sprite-run

# Run basic tests
test:
	go test -v ./...

# Show help
help:
	@echo "Available targets:"
	@echo "  build   - Build the sprite-run binary"
	@echo "  clean   - Clean build artifacts"
	@echo "  install - Install binary to ~/bin"
	@echo "  test    - Run tests"
	@echo "  help    - Show this help"

# Default target
all: build
