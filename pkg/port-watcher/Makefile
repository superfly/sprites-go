.PHONY: test test-unit clean deps coverage help

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

# Run all tests directly; let failures surface
test:
	go test -v -race ./...

# Run unit tests locally
test-unit:
	@echo "Running unit tests locally..."
	go test -v ./...


# Generate coverage report
coverage: test
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