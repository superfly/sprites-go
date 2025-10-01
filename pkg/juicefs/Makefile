# Makefile for pkg/juicefs

# Default target
.PHONY: test
test:
	@echo "Running JuiceFS package tests..."
	@cd ../.. && $(MAKE) test ARGS="go test ./pkg/juicefs/..."

# Run tests with verbose output
.PHONY: test-verbose
test-verbose:
	@echo "Running JuiceFS package tests (verbose)..."
	@cd ../.. && $(MAKE) test ARGS="go test ./pkg/juicefs/... -v"

# Run tests with coverage
.PHONY: test-coverage
test-coverage:
	@echo "Running JuiceFS package tests with coverage..."
	@cd ../.. && $(MAKE) test ARGS="go test ./pkg/juicefs/... -cover"

# Run only short tests (non-Linux)
.PHONY: test-short
test-short:
	@echo "Running JuiceFS package short tests..."
	@cd ../.. && $(MAKE) test ARGS="go test ./pkg/juicefs/... -short"

# Run tests in Docker (for Linux-specific tests)
.PHONY: test-docker
test-docker:
	@echo "Running JuiceFS package tests in Docker..."
	@cd ../.. && $(MAKE) test-docker ARGS="go test ./pkg/juicefs/..."

# Clean test cache
.PHONY: clean
clean:
	@echo "Cleaning test cache..."
	@go clean -testcache

# Help
.PHONY: help
help:
	@echo "Available targets:"
	@echo "  test          - Run all tests"
	@echo "  test-verbose  - Run tests with verbose output"
	@echo "  test-coverage - Run tests with coverage"
	@echo "  test-short    - Run only short tests (skips Linux-specific)"
	@echo "  test-docker   - Run tests in Docker (includes Linux-specific)"
	@echo "  clean         - Clean test cache"
	@echo "  help          - Show this help message"