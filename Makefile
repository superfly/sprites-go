.PHONY: test test-machine build build-linux test-sdks help

test:
	./scripts/run-tests.sh

# Build client and server binaries
build:
	@echo "Building server..."
	go build -o dist/server ./server
	@echo "Building client..."
	go build -o dist/sprite ./client

# Build Linux binaries
build-linux:
	@echo "Building Linux server..."
	GOOS=linux GOARCH=amd64 go build -o dist/server-linux ./server
	@echo "Building Linux client..."
	GOOS=linux GOARCH=amd64 go build -o dist/sprite-linux ./client

# Run machine integration tests
test-machine: build
	@echo "Running machine integration tests..."
		@echo "Make sure FLY_APP_NAME and SPRITE_TOKEN are set (see tests/README.md for details)"
	cd tests && make test

# Test all SDKs
test-sdks:
	@echo "Building base sprite-env image..."
	docker build -t sprite-env-base:test .
	@echo "Building SDK test Docker image..."
	docker build -f sdks/Dockerfile.test -t sprite-sdks-test .
	@echo "Running all SDK tests..."
	docker run --rm --privileged sprite-sdks-test

# Show available targets
help:
	@echo "Available targets:"
	@echo "  test         - Run unit tests"
	@echo "  build        - Build client and server binaries"
	@echo "  build-linux  - Build Linux binaries with -linux suffix"
	@echo "  test-machine - Run machine integration tests (requires FLY_APP_NAME and SPRITE_TOKEN)"
	@echo "  test-sdks    - Test all SDKs in Docker"
	@echo "  help         - Show this help message"