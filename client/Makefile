.PHONY: build clean test install

# Default target
all: build

# Build the binary
build:
	go build -o sprite

# Install to GOPATH/bin or GOBIN
install:
	go install

# Clean build artifacts
clean:
	rm -f sprite

# Run tests (if any)
test:
	go test ./...

# Build for multiple platforms
build-all:
	GOOS=linux GOARCH=amd64 go build -o sprite-linux-amd64
	GOOS=darwin GOARCH=amd64 go build -o sprite-darwin-amd64
	GOOS=darwin GOARCH=arm64 go build -o sprite-darwin-arm64
	GOOS=windows GOARCH=amd64 go build -tags clientonly -o sprite-windows-amd64.exe

# Run with example
run-example: build
		@echo "Make sure SPRITE_URL and SPRITE_TOKEN are set! (see client/README.md for details)"
	./sprite exec echo "Hello from sprite" 