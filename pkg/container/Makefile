.PHONY: test clean deps

test:
	go test -v ./...

clean:
	go clean
	rm -f /tmp/container-tty-*.sock

deps:
	go mod download
	go mod tidy