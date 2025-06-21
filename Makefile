.PHONY: test test-machine help

test:
	./scripts/run-tests.sh

# Run machine integration tests
test-machine:
	@echo "Running machine integration tests..."
	@echo "Make sure FLY_APP_NAME and SPRITE_TOKEN are set"
	cd tests && make test

# Show available targets
help:
	@echo "Available targets:"
	@echo "  test         - Run unit tests"
	@echo "  test-machine - Run machine integration tests (requires FLY_APP_NAME and SPRITE_TOKEN)"
	@echo "  help         - Show this help message"