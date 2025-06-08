.PHONY: build test clean docker-build-test

# Build the server
build:
	go build -o tmp/sprite-env .

# Run integration tests
test: build
	TSCRIPTS_DIR=$$(cd test-scripts && pwd) go test -v -failfast ./tests

# Clean build artifacts
clean:
	rm -rf tmp/

# Build Docker image and run tests using Docker
docker-build-test:
	docker build -t sprite-env-test -f Dockerfile.test .
	docker run --rm sprite-env-test 