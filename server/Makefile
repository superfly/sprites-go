.PHONY: build test test-integration test-unit test-supervisor clean docker-build-test release-all release-linux-amd64 release-linux-arm64 release-darwin-amd64 release-darwin-arm64

# Build the server
build:
	go build -o tmp/sprite-env .

# Run all tests (unit first, then integration)
test: test-packages test-unit test-integration

test-packages: test-supervisor test-docker

# Run integration tests
test-integration: build
	TSCRIPTS_DIR=$$(cd test-scripts && pwd) go test -v -failfast ./tests

# Run unit tests
test-unit:
	go test -v -failfast ./lib/...

# Run supervisor package tests specifically
test-supervisor:
	cd packages/supervisor && go test -v -failfast ./...

test-juicefs:
	cd packages/juicefs && make test-docker

# Clean build artifacts
clean:
	rm -rf tmp/
	rm -rf dist/

# Build Docker image and run tests using Docker
# Same resources as github actions
docker-build-test:
	docker build -t sprite-env-test -f Dockerfile.test .
	docker run --rm --cpus="2" --memory="7g" sprite-env-test 

# Release builds
VERSION ?= dev

release-all: release-linux-amd64 release-linux-arm64 release-darwin-amd64 release-darwin-arm64
	@echo "All release binaries built in dist/"

release-linux-amd64:
	@mkdir -p dist
	CGO_ENABLED=0 GOOS=linux GOARCH=amd64 go build \
		-ldflags="-w -s -X main.version=$(VERSION)" \
		-o dist/sprite-env-linux-amd64 .
	@echo "Built: dist/sprite-env-linux-amd64"

release-linux-arm64:
	@mkdir -p dist
	CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build \
		-ldflags="-w -s -X main.version=$(VERSION)" \
		-o dist/sprite-env-linux-arm64 .
	@echo "Built: dist/sprite-env-linux-arm64"

release-darwin-amd64:
	@mkdir -p dist
	CGO_ENABLED=0 GOOS=darwin GOARCH=amd64 go build \
		-ldflags="-w -s -X main.version=$(VERSION)" \
		-o dist/sprite-env-darwin-amd64 .
	@echo "Built: dist/sprite-env-darwin-amd64"

release-darwin-arm64:
	@mkdir -p dist
	CGO_ENABLED=0 GOOS=darwin GOARCH=arm64 go build \
		-ldflags="-w -s -X main.version=$(VERSION)" \
		-o dist/sprite-env-darwin-arm64 .
	@echo "Built: dist/sprite-env-darwin-arm64" 