.PHONY: test test-unit test-integration test-examples test-all test-docker clean coverage help

# Default target
default: test

# Help target
help:
	@echo "Available targets:"
	@echo "  test              - Run all tests (unit + integration if binaries available)"
	@echo "  test-unit         - Run unit tests only"
	@echo "  test-integration  - Run integration tests (requires juicefs/litestream)"
	@echo "  test-examples     - Run example tests (requires environment variables)"
	@echo "  test-all          - Run all tests including examples"
	@echo "  test-docker       - Run all tests in Docker container"
	@echo "  coverage          - Generate test coverage report"
	@echo "  clean             - Clean test artifacts"

# Run all tests
test: test-docker

# Run unit tests only
test-unit:
	@echo "Running unit tests..."
	go test -v -race -coverprofile=coverage.out -run '^Test' ./...

# Run integration tests (requires binaries)
test-integration:
	@echo "Running integration tests..."
	@if ! command -v juicefs >/dev/null 2>&1; then \
		echo "Error: juicefs binary not found in PATH"; \
		exit 1; \
	fi
	@if ! command -v litestream >/dev/null 2>&1; then \
		echo "Error: litestream binary not found in PATH"; \
		exit 1; \
	fi
	go test -v -race -tags=integration ./...

# Run example tests (requires environment variables)
test-examples:
	@echo "Running example tests..."
	@echo "Note: Examples require SPRITE_S3_* environment variables to be set"
	go test -v -run '^Example' ./...

# Run all tests including examples
test-all:
	@echo "Running all tests including examples..."
	@if command -v juicefs >/dev/null 2>&1 && command -v litestream >/dev/null 2>&1; then \
		echo "JuiceFS and Litestream found, running all tests including integration..."; \
		go test -v -race -tags=integration -coverprofile=coverage.out ./...; \
	else \
		echo "JuiceFS or Litestream not found, running unit tests only..."; \
		go test -v -race -coverprofile=coverage.out ./...; \
	fi

# Build Docker test image
docker-build:
	@echo "Building test Docker image..."
	docker build -t juicefs-test -f Dockerfile.test ../..

# Run tests in Docker container
test-docker: docker-build
	@echo "Running tests in Docker..."
	@docker run --rm --privileged -v $(PWD):/host-packages juicefs-test

# Generate coverage report
coverage: test
	@echo "Generating coverage report..."
	go tool cover -html=coverage.out -o coverage.html
	@echo "Coverage report generated at coverage.html"

# Clean test artifacts
clean:
	@echo "Cleaning test artifacts..."
	rm -f coverage.out coverage.html
	@if docker images | grep -q juicefs-test; then \
		docker rmi juicefs-test; \
		echo "Removed Docker test image"; \
	fi