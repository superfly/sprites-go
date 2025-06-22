.PHONY: test test-machine build help

test:
	./scripts/run-tests.sh

# Build client and server binaries
build:
	@echo "Building server..."
	go build -o dist/server ./server
	@echo "Building client..."
	go build -o dist/sprite ./client

# Run machine integration tests
test-machine: build
	@echo "Running machine integration tests..."
	@echo "Make sure FLY_APP_NAME and SPRITE_TOKEN are set"
	cd tests && make test

# Show available targets
help:
	@echo "Available targets:"
	@echo "  test         - Run unit tests"
	@echo "  build        - Build client and server binaries"
	@echo "  test-machine - Run machine integration tests (requires FLY_APP_NAME and SPRITE_TOKEN)"
	@echo "  help         - Show this help message"