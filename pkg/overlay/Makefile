# Makefile for pkg/overlay

# Default target
.PHONY: test
test:
	@echo "Running overlay package tests..."
	@cd ../.. && $(MAKE) test ARGS="go test ./pkg/overlay/..."

# Run tests with verbose output
.PHONY: test-verbose
test-verbose:
	@echo "Running overlay package tests (verbose)..."
	@cd ../.. && $(MAKE) test ARGS="go test ./pkg/overlay/... -v"

# Run tests with coverage
.PHONY: test-coverage
test-coverage:
	@echo "Running overlay package tests with coverage..."
	@cd ../.. && $(MAKE) test ARGS="go test ./pkg/overlay/... -cover"

# Run only short tests (non-Linux)
.PHONY: test-short
test-short:
	@echo "Running overlay package short tests..."
	@cd ../.. && $(MAKE) test ARGS="go test ./pkg/overlay/... -short"

# Run tests in Docker (for Linux-specific tests)
.PHONY: test-docker
test-docker:
	@echo "Running overlay package tests in Docker..."
	@cd ../.. && $(MAKE) test-docker ARGS="go test ./pkg/overlay/..."

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
