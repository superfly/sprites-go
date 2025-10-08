# Sprites SDK Development Guide

This is a guide for building SDKs inside `sdks/`. It is written to serve as clear context for Claude code generation while you implement a new SDK. The guidance only references content in `sdks/` and its submodules.

## Submodule setup

Each SDK lives in its own GitHub repository and is included here as a git submodule. The existing SDKs are:
- Go: `sdks/go` → `github.com/superfly/sprites-go`
- JavaScript/TypeScript: `sdks/js` → `github.com/superfly/sprites-js`

To add a new SDK submodule (example for a `<lang>` SDK):

```bash
git submodule add https://github.com/superfly/sprites-<lang>.git sdks/<lang>
git submodule update --init --recursive
```

To update a submodule to a newer commit, tag, or branch:

```bash
cd sdks/<lang>
git fetch
git checkout <branch-or-tag-or-commit>
cd -
git add sdks/<lang>
git commit -m "Update <lang> SDK submodule"
```

The SDK’s source code, issues, tags, and releases live in the SDK’s own repository. This repository tracks those via submodule pointers under `sdks/`.

## Scope and Requirements

- Implement only two core capabilities initially:
  - Sprite lifecycle: create (and optionally destroy for cleanup tooling)
  - Command execution: exec that mirrors the host language’s standard process API
- Provide a `test-cli` program that conforms to the existing SDK CLIs in `sdks/go/test-cli` and `sdks/js/test-node-cli` so it can be driven by the shared test harness in `sdks/test`.

## API Shape Expectations

- Exec must mirror the host language’s native process APIs:
  - Go SDK model: `sprite.Command(...)` matching `exec.Command`
  - Node SDK model: `sprite.spawn(...)` matching `child_process.spawn`
- Keep naming and behavior consistent with the language norms (environment, working directory, TTY, pipes/streams, exit codes, errors).
- Only implement: sprite create and exec. Other management calls can be added later.

## Test CLI Contract (Required)

Your SDK must include a `test-cli` that matches the flags/behavior used by `sdks/test`:
- Flags (align with Go/Node CLIs):
  - `-base-url <url>`: API base URL (default: https://api.sprites.dev)
  - `-sprite <name>`: sprite name for exec commands
  - `-dir <path>`: working directory
  - `-env key=value[,key=value]`: environment variables
  - `-tty`, `-tty-rows <int>`, `-tty-cols <int>`
  - `-detachable`, `-session-id <id>` (session support when available)
  - `-timeout <duration>` (e.g., 10s)
  - `-output stdout|combined|exit-code|default`
  - `-log-target <path>`: append-only JSON event log (see existing CLIs)
- Subcommands that do not require `-sprite`:
  - `create <sprite-name>`
  - `destroy <sprite-name>` (optional but useful for cleanup)
- Exec mode behavior must map to output modes used in tests:
  - `stdout`: print stdout only, exit non-zero on failure
  - `combined`: print combined stdout+stderr, exit non-zero on failure
  - `exit-code`: run command, do not print, exit with the command’s exit code
  - `default`: stream stdin/stdout/stderr directly
- The CLI should emit structured JSON logs to `-log-target` (see existing CLIs) for debugging and port notifications.

See reference implementations:
- Go: `sdks/go/test-cli/`
- Node: `sdks/js/test-node-cli/`

## Environment Variables for Test Harness

The shared test harness in `sdks/test` expects the following environment variables:
- `SDK_TEST_COMMAND`: path to your built `test-cli` executable
- `SPRITES_TEST_TOKEN`: token for authenticated calls to the API
- `SPRITES_BASE_URL` (optional): API base URL; defaults to `https://api.sprites.dev`

## Integration Tests

- Add integration tests under `sdks/test/` (the suite is SDK-agnostic and driven by `SDK_TEST_COMMAND`).
- The tests will be run against a real Sprite org/token if `SPRITES_TEST_TOKEN` is set in the environment.
- Review the existing Go-driven tests in `sdks/test/` for expected behaviors (stdout streaming, fast commands, concurrency, stdin, TTY, no hanging).

## CI Integration

- Add a block to the SDK GitHub Actions workflow that builds your `test-cli` and runs the test suite by pointing `SDK_TEST_COMMAND` to it.
- The workflow should set `SPRITES_TEST_TOKEN` (from repository secrets) and optionally `SPRITES_BASE_URL`.
- Keep the job self-contained within `sdks/` (do not depend on non-SDK codepaths).

## Checklist

- Provide `test-cli` with the required flags and subcommands
- Implement sprite create and exec aligned with language-native process APIs
- Ensure structured logging compatibility (`-log-target`)
- Verify integration tests pass with a real token via `sdks/test`
- Add/update the SDK test workflow block to exercise your `test-cli`