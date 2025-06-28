.PHONY: test test-unit test-integration test-integration-basic test-tty test-checkpoint test-docker install dev-install lint format clean help

# Default target
help:
	@echo "Available targets:"
	@echo "  install              - Install the SDK"
	@echo "  dev-install          - Install the SDK in development mode with test dependencies"
	@echo "  test                 - Run all tests"
	@echo "  test-unit            - Run unit tests only"
	@echo "  test-integration     - Run all integration tests (requires server binary)"
	@echo "  test-integration-basic - Run basic integration tests (skip TTY and checkpoint)"
	@echo "  test-tty             - Run TTY tests only"
	@echo "  test-checkpoint      - Run checkpoint/restore tests only (requires JuiceFS)"
	@echo "  test-docker          - Run all tests in Docker container"
	@echo "  lint                 - Run code linting"
	@echo "  format               - Format code with black"
	@echo "  clean                - Clean up generated files"
	@echo "  help                 - Show this help message"

# Install the SDK
install:
	pip install .

# Install in development mode with test dependencies
dev-install:
	pip install -e .
	pip install pytest pytest-cov pytest-timeout pytest-mock

# Run all tests
test: test-unit test-integration

# Run unit tests only
test-unit:
	pytest -v tests/test_unit.py

# Run integration tests (requires server)
test-integration:
	@if [ -z "$${SPRITE_SERVER_BINARY}" ] && [ ! -f "../../dist/server" ]; then \
		echo "Error: Server binary not found. Run 'make build' in the project root first."; \
		exit 1; \
	fi
	SPRITE_SERVER_BINARY=$${SPRITE_SERVER_BINARY:-../../dist/server} pytest -v tests/test_integration.py

# Run only basic integration tests (skip TTY and checkpoint tests)
test-integration-basic:
	@if [ -z "$${SPRITE_SERVER_BINARY}" ] && [ ! -f "../../dist/server" ]; then \
		echo "Error: Server binary not found. Run 'make build' in the project root first."; \
		exit 1; \
	fi
	SPRITE_SERVER_BINARY=$${SPRITE_SERVER_BINARY:-../../dist/server} pytest -v tests/test_integration.py -m "not tty and not checkpoint"

# Run TTY tests only
test-tty:
	@if [ -z "$${SPRITE_SERVER_BINARY}" ] && [ ! -f "../../dist/server" ]; then \
		echo "Error: Server binary not found. Run 'make build' in the project root first."; \
		exit 1; \
	fi
	SPRITE_SERVER_BINARY=$${SPRITE_SERVER_BINARY:-../../dist/server} pytest -v tests/test_integration.py -m tty

# Run checkpoint tests only
test-checkpoint:
	@if [ -z "$${SPRITE_SERVER_BINARY}" ] && [ ! -f "../../dist/server" ]; then \
		echo "Error: Server binary not found. Run 'make build' in the project root first."; \
		exit 1; \
	fi
	SPRITE_SERVER_BINARY=$${SPRITE_SERVER_BINARY:-../../dist/server} pytest -v tests/test_integration.py -m checkpoint

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

# Lint the code
lint:
	@which flake8 > /dev/null || (echo "Installing flake8..." && pip install flake8)
	flake8 sprites/ tests/ --max-line-length=100 --ignore=E501,W503

# Format code with black
format:
	@which black > /dev/null || (echo "Installing black..." && pip install black)
	black sprites/ tests/ examples/

# Clean up
clean:
	rm -rf build/ dist/ *.egg-info/
	find . -type d -name __pycache__ -exec rm -rf {} +
	find . -type f -name "*.pyc" -delete
	find . -type f -name "*.pyo" -delete
	find . -type f -name "*~" -delete
	find . -type f -name ".coverage" -delete
	rm -rf .pytest_cache/