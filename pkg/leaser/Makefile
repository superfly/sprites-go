.PHONY: test
test:
	go test -v

.PHONY: test-race
test-race:
	go test -v -race

.PHONY: test-cover
test-cover:
	go test -v -cover -coverprofile=coverage.out
	go tool cover -html=coverage.out -o coverage.html

.PHONY: bench
bench:
	go test -bench=. -benchmem

.PHONY: clean
clean:
	rm -f coverage.out coverage.html

.PHONY: lint
lint:
	golangci-lint run

.PHONY: fmt
fmt:
	go fmt ./...