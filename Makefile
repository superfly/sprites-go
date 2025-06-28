.PHONY: test test-machine build build-linux test-sdks help

test:
	./scripts/run-tests.sh

# Build client and server binaries
build: docs
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
test-sdks: build-linux
	@echo "Testing SDKs..."
	@echo "Copying Linux binaries for Docker build..."
	@mkdir -p sdks/python/dist
	@cp dist/server-linux sdks/python/dist/server
	@cp dist/sprite-linux sdks/python/dist/sprite
	@echo "Running Python SDK tests..."
	cd sdks/python && make test-docker

# Show available targets
help:
	@echo "Available targets:"
	@echo "  test         - Run unit tests"
	@echo "  build        - Build client and server binaries"
	@echo "  build-linux  - Build Linux binaries with -linux suffix"
	@echo "  test-machine - Run machine integration tests (requires FLY_APP_NAME and SPRITE_TOKEN)"
	@echo "  test-sdks    - Test all SDKs in Docker"
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
