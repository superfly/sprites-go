.PHONY: build test test-integration test-unit clean docker-build-test

# Build the server
build:
	go build -o tmp/sprite-env .

# Run all tests (unit first, then integration)
test: test-unit test-integration

# Run integration tests
test-integration: build
	TSCRIPTS_DIR=$$(cd test-scripts && pwd) go test -v -failfast ./tests

# Run unit tests
test-unit:
	go test -v -failfast ./lib/...

# Clean build artifacts
clean:
	rm -rf tmp/

# Build Docker image and run tests using Docker
# Same resources as github actions
docker-build-test:
	docker build -t sprite-env-test -f Dockerfile.test .
	docker run --rm --cpus="2" --memory="7g" sprite-env-test 