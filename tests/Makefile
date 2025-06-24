.PHONY: test test-deploy test-zombie test-checkpoint clean help

# Default test timeout
TIMEOUT ?= 10m

# Run all integration tests
test:
	@echo "Running all integration tests..."
	GOWORK=off go test -v --failfast -timeout $(TIMEOUT)

# Run only deployment test
test-deploy:
	@echo "Running deployment test..."
	GOWORK=off go test -v -timeout $(TIMEOUT) -run TestDeployAndFunctionality/Deploy

# Run only zombie cleanup test  
test-zombie:
	@echo "Running zombie cleanup test..."
	GOWORK=off go test -v -timeout $(TIMEOUT) -run TestDeployAndFunctionality/ZombieCleanup

# Run only checkpoint/restore test
test-checkpoint:
	@echo "Running checkpoint/restore test..."
	GOWORK=off go test -v -timeout $(TIMEOUT) -run TestDeployAndFunctionality/CheckpointRestore

# Run only TTY test
test-tty:
	@echo "Running TTY functionality test..."
	GOWORK=off go test -v -timeout $(TIMEOUT) -run TestTTYFunctionality

# Clean up built artifacts
clean:
	@echo "Cleaning up..."
	rm -rf ../dist

# Show help
help:
	@echo "Available targets:"
	@echo "  test             - Run all integration tests"
	@echo "  test-deploy      - Run only deployment test"
	@echo "  test-zombie      - Run only zombie cleanup test"
	@echo "  test-checkpoint  - Run only checkpoint/restore test"
	@echo "  clean            - Remove built artifacts"
	@echo ""
	@echo "Required environment variables:"
	@echo "  FLY_APP_NAME    - Your Fly.io app name"
	@echo "  SPRITE_TOKEN    - Authentication token for Sprite API"
	@echo ""
	@echo "Optional environment variables:"
	@echo "  FLY_API_TOKEN   - Fly API token (will use flyctl if not set)"
	@echo "  TIMEOUT         - Test timeout (default: 10m)" 