.PHONY: test test-unit test-docker docker-build clean deps coverage help

# Default target
default: test

# Help target
help:
	@echo "Available targets:"
	@echo "  test          - Run tests in Docker container (default)"
	@echo "  test-unit     - Run unit tests locally"
	@echo "  test-docker   - Run tests in Docker container"
	@echo "  docker-build  - Build Docker test image"
	@echo "  coverage      - Generate test coverage report"
	@echo "  clean         - Clean test artifacts"
	@echo "  deps          - Download and tidy dependencies"

# Run tests in Docker container (default)
test: test-docker

# Run unit tests locally
test-unit:
	@echo "Running unit tests locally..."
	go test -v ./...

# Build Docker test image
docker-build:
	@echo "Building test Docker image..."
	docker build -t port-watcher-test -f Dockerfile.test ../..

# Run tests in Docker container
test-docker: docker-build
	@echo "Running tests in Docker..."
	@docker run --rm --privileged -v $(PWD):/host-packages port-watcher-test

# Generate coverage report
coverage: test-docker
	@echo "Generating coverage report..."
	@if [ -f coverage.out ]; then \
		go tool cover -html=coverage.out -o coverage.html; \
		echo "Coverage report generated at coverage.html"; \
	else \
		echo "No coverage.out file found. Run tests first."; \
	fi

# Clean test artifacts
clean:
	@echo "Cleaning test artifacts..."
	rm -f coverage.out coverage.html
	@if docker images | grep -q port-watcher-test; then \
		docker rmi port-watcher-test; \
		echo "Removed Docker test image"; \
	fi

# Download and tidy dependencies
deps:
	go mod download
	go mod tidy