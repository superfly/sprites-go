.PHONY: test test-docker test-clean test-rebuild test-machine build build-linux test-cli help

# Forward any extra args after `make test` to the script
TEST_ARGS := $(filter-out test,$(MAKECMDGOALS))

# Run all tests in Docker container (mirrors production environment)
test:
	bash ./scripts/run-tests-docker.sh $(TEST_ARGS) $(ARGS)

# Alias for backwards compatibility
test-docker: test

# Clean up persistent test container
test-clean:
	@echo "Stopping and removing test container..."
	@docker stop sprite-test-container 2>/dev/null || true
	@docker rm sprite-test-container 2>/dev/null || true

# Force rebuild the test image
test-rebuild: test-clean
	@echo "Forcing rebuild of test image..."
	docker build -f Dockerfile.test -t sprite-env-tests .
	@echo "Test container cleaned up"

# Build client and server binaries
build:
	@echo "Building server..."
	go build -o dist/server ./server
	@echo "Building client..."
	go build -o dist/sprite ./client

# Build test-cli binary
test-cli:
	@echo "Building test-cli..."
	cd sdk && make test-cli

# Treat unknown goals (used as test args) as no-ops so make doesn't error
%:
	@:
