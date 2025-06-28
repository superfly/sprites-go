.PHONY: test test-docker install dev-install clean help

# Default target
help:
	@echo "Available targets:"
	@echo "  install              - Install the SDK"
	@echo "  dev-install          - Install the SDK in development mode with test dependencies"
	@echo "  test                 - Run Docker tests"
	@echo "  test-docker          - Run all tests in Docker container"
	@echo "  clean                - Clean up generated files"
	@echo "  help                 - Show this help message"

# Install the SDK
install:
	pip install .

# Install in development mode with test dependencies
dev-install:
	pip install -e .
	pip install pytest pytest-cov pytest-timeout pytest-mock

# Run Docker tests (default test target)
test: test-docker

# Run tests in Docker container
test-docker:
	@if [ ! -f "dist/server" ]; then \
		echo "Error: Linux server binary not found. Run 'make test-sdks' from project root first."; \
		exit 1; \
	fi
	@echo "Building Docker test image..."
	docker build -f Dockerfile.test -t sprites-python-test .
	@echo "Running tests in Docker..."
	docker run --rm --privileged sprites-python-test

# Clean up
clean:
	rm -rf build/ dist/ *.egg-info/
	find . -type d -name __pycache__ -exec rm -rf {} +
	find . -type f -name "*.pyc" -delete
	find . -type f -name "*.pyo" -delete
	find . -type f -name "*~" -delete
	find . -type f -name ".coverage" -delete
	rm -rf .pytest_cache/