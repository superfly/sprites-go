.PHONY: test test-machine build help

test:
	./scripts/run-tests.sh

# Build client and server binaries
build: docs
	@echo "Building server..."
	go build -o dist/server ./server
	@echo "Building client..."
	go build -o dist/sprite ./client

# Run machine integration tests
test-machine: build
	@echo "Running machine integration tests..."
		@echo "Make sure FLY_APP_NAME and SPRITE_TOKEN are set (see tests/README.md for details)"
	cd tests && make test

# Show available targets
help:
	@echo "Available targets:"
	@echo "  test         - Run unit tests"
	@echo "  build        - Build client and server binaries"
	@echo "  test-machine - Run machine integration tests (requires FLY_APP_NAME and SPRITE_TOKEN)"
	@echo "  help         - Show this help message"


# Generate OpenAPI documentation
docs:
	@echo "🔨 Generating OpenAPI documentation..."
	@mkdir -p server/api/handlers/static
	@go run packages/api-docs/cmd/generate/main.go \
		-source ./server \
		-output ./server/api/handlers/static/openapi.json \
		-title "Sprites API" \
		-version "1.0.0" \
		-server "https://api.sprites.dev/v1"
	@echo "✅ OpenAPI spec generated at ./server/api/handlers/static/openapi.json"