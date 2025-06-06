.PHONY: build test clean

# Build the server
build:
	go build -o tmp/sprite-env .

# Run integration tests
test: build
	TSCRIPTS_DIR=$$(cd test-scripts && pwd) go test -v ./tests

# Clean build artifacts
clean:
	rm -rf tmp/ 