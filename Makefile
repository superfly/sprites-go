.PHONY: test test-docker test-machine build build-linux help

test:
	./scripts/run-tests.sh $(ARGS)

# Build and run tests inside Docker (requires Docker; uses --privileged for FUSE)
test-docker:
	bash ./scripts/run-tests-docker.sh $(ARGS)

# Build client and server binaries
build:
	@echo "Building server..."
	go build -o dist/server ./server
	@echo "Building client..."
	go build -o dist/sprite ./client