.PHONY: build test clean

# Build the server
build:
	go build -o sprite-env

# Run tests for each directory in test-scripts
test: build
	@for dir in test-scripts/*/; do \
		echo "Running test for $$dir"; \
		if [ -f "$$dir/supervised-process.sh" ]; then \
			SUPERVISED_PROCESS="$$dir/supervised-process.sh"; \
		elif [ -f "$$dir/supervised_process.sh" ]; then \
			SUPERVISED_PROCESS="$$dir/supervised_process.sh"; \
		else \
			echo "No supervised process script found in $$dir"; \
			exit 1; \
		fi; \
		./sprite-env -debug -test-dir "$$dir" -- "$$SUPERVISED_PROCESS" & \
		PID=$$!; \
		echo "Started process with PID $$PID"; \
		sleep 2; \
		echo "Sending SIGTERM to $$PID"; \
		kill -TERM $$PID || echo "Failed to send SIGTERM"; \
		echo "Waiting for process $$PID to exit"; \
		wait $$PID; \
		EXIT_CODE=$$?; \
		echo "Process exited with code $$EXIT_CODE"; \
		if [ $$EXIT_CODE -ne 0 ] && [ $$EXIT_CODE -ne 143 ]; then \
			echo "Test failed with exit code $$EXIT_CODE"; \
			exit $$EXIT_CODE; \
		fi; \
	done

# Clean build artifacts
clean:
	rm -f sprite-env 