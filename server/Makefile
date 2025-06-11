.PHONY: build test test-integration test-unit clean docker-build-test

# Build the server
build:
	go build -o tmp/sprite-env .

# Run all tests (integration + unit)
test: test-integration test-unit

# Run integration tests
test-integration: build
	TSCRIPTS_DIR=$$(cd test-scripts && pwd) go test -v -failfast ./tests

# Run unit tests
test-unit:
	go test -v -failfast ./lib

# Clean build artifacts
clean:
	rm -rf tmp/

# Build Docker image and run tests using Docker
docker-build-test:
	docker build -t sprite-env-test -f Dockerfile.test .
	docker run --rm sprite-env-test 