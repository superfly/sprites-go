# AGENTS.md

`sprites-go` is the Go SDK for Fly.io Sprites, with an `exec.Cmd`-style API for running commands
on Sprites. The Go version is in `go.mod`. The SDK is the root package; `examples/` and
`test-cli/` are separate Go modules that point back at it with a `replace` directive.

## Test

```sh
go test ./...
```

CI runs this on Linux, macOS and Windows. Tests sit next to the code they test.

`TestSpriteLifecycle` in `exec_test.go` skips unless `SPRITES_TEST_TOKEN` is set. With a token it
creates and destroys a real Sprite in that token's organization, which costs money, so don't set
it unless asked. `./run_integration_tests.sh` runs the `TestSprite*` tests with a token.

## Lint

```sh
golangci-lint run ./...
pre-commit run --all-files   # whitespace, go mod tidy, golangci-lint
```

## Releases

A release commit ("Prepare vX.Y.Z release") adds a `CHANGELOG.md` entry. Maintainers then run
`scripts/bump_version.sh` (or `scripts/bump_version.sh prerel`), which tags and pushes the release; the
`release.yml` workflow publishes it. Don't tag unless asked.
