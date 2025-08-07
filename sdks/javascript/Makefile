.PHONY: build-base build-test test test-dev run-test-env clean

# Build the base sprite-env image (only needed once or when base changes)
build-base:
	docker buildx build --load -t sprite-env-base:test -f ../../Dockerfile ../..

# Build the test environment image (only needed once or when test env changes)
build-test: build-base
	docker build -t sprite-javascript-test-env -f Dockerfile.test .

# Full test with build (slower, for CI or major changes)
test: build-test
	docker run --rm --privileged \
		-v $(PWD):/sdk \
		sprite-javascript-test-env

# Fast development test (reuses existing test environment, mounts source)
test-dev:
	@if ! docker image inspect sprite-javascript-test-env >/dev/null 2>&1; then \
		echo "Test environment not built. Running 'make build-test'..."; \
		$(MAKE) build-test; \
	fi
	docker run --rm --privileged \
		-v $(PWD):/sdk \
		sprite-javascript-test-env

# Run interactive test environment for debugging
run-test-env:
	@if ! docker image inspect sprite-javascript-test-env >/dev/null 2>&1; then \
		echo "Test environment not built. Running 'make build-test'..."; \
		$(MAKE) build-test; \
	fi
	docker run -it --rm --privileged \
		-v $(PWD):/sdk \
		--entrypoint /bin/bash \
		sprite-javascript-test-env

# Clean up test containers and images
clean:
	docker rmi sprite-javascript-test-env 2>/dev/null || true
	docker rmi sprite-env-base:test 2>/dev/null || true
	docker system prune -f