.PHONY: build test clean help

# Default target
all: build

# Build the test-cli binary (required for tests)
build:
	@echo "Building test-cli binary..."
	cd ../go/test-cli && go build -o test-cli main.go

# Run a specific test
test: build
	@echo "Running sprite SDK tests..."
	@if [ -z "$(SPRITES_TEST_TOKEN)" ]; then \
		echo "Error: SPRITES_TEST_TOKEN environment variable is required"; \
		exit 1; \
	fi
	@if [ -z "$(SDK_TEST_COMMAND)" ]; then \
		echo "Error: SDK_TEST_COMMAND environment variable is required"; \
		echo "Example: SDK_TEST_COMMAND=../go/test-cli/test-cli make test"; \
		exit 1; \
	fi
	go test -v -run $(TEST) $(ARGS)

# Run all tests
test-all: build
	@echo "Running all sprite SDK tests..."
	@if [ -z "$(SPRITES_TEST_TOKEN)" ]; then \
		echo "Error: SPRITES_TEST_TOKEN environment variable is required"; \
		exit 1; \
	fi
	@if [ -z "$(SDK_TEST_COMMAND)" ]; then \
		echo "Error: SDK_TEST_COMMAND environment variable is required"; \
		echo "Example: SDK_TEST_COMMAND=../go/test-cli/test-cli make test-all"; \
		exit 1; \
	fi
	go test -v $(ARGS)

# Clean build artifacts
clean:
	rm -f ../go/test-cli/test-cli

# Show help
help:
	@echo "Sprite SDK Test Suite"
	@echo "===================="
	@echo ""
	@echo "Available targets:"
	@echo "  build     - Build the test-cli binary"
	@echo "  test      - Run a specific test (requires TEST env var)"
	@echo "  test-all  - Run all tests"
	@echo "  clean     - Remove build artifacts"
	@echo "  help      - Show this help message"
	@echo ""
	@echo "Environment variables:"
	@echo "  SPRITES_TEST_TOKEN - Authentication token (required)"
	@echo "  SDK_TEST_COMMAND  - Path to SDK test binary (required)"
	@echo "  TEST              - Specific test to run (for 'test' target)"
	@echo ""
	@echo "Available tests:"
	@echo "  TestStdoutStreaming   - Test stdout/stderr streaming"
	@echo "  TestFastCommands      - Test fast running commands don't miss stdout"
	@echo "  TestConcurrentCommands - Test 10 concurrent fast running commands"
	@echo "  TestNoHanging         - Test no exec calls hang"
	@echo "  TestStdin             - Test stdin works properly"
	@echo "  TestTTY               - Test TTY functionality"
	@echo ""
	@echo "Examples:"
	@echo "  SDK_TEST_COMMAND=../go/test-cli/test-cli make test-all"
	@echo "  SDK_TEST_COMMAND=../go/test-cli/test-cli make test TEST=TestStdoutStreaming"
	@echo "  SDK_TEST_COMMAND=../go/test-cli/test-cli make test TEST=TestConcurrentCommands ARGS='-timeout=60s'"
