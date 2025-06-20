.PHONY: build clean test install

# Default target
all: build

# Build the binary
build:
	go build -o sprite-client

# Install to GOPATH/bin or GOBIN
install:
	go install

# Clean build artifacts
clean:
	rm -f sprite-client

# Run tests (if any)
test:
	go test ./...

# Build for multiple platforms
build-all:
	GOOS=linux GOARCH=amd64 go build -o sprite-client-linux-amd64
	GOOS=darwin GOARCH=amd64 go build -o sprite-client-darwin-amd64
	GOOS=darwin GOARCH=arm64 go build -o sprite-client-darwin-arm64
	GOOS=windows GOARCH=amd64 go build -o sprite-client-windows-amd64.exe

# Run with example
run-example: build
	@echo "Make sure SPRITE_URL and SPRITE_TOKEN are set!"
	./sprite-client exec echo "Hello from sprite" 