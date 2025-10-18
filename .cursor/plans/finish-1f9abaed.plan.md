<!-- 1f9abaed-c449-4693-821c-1f848a1d6aa7 9218e30d-2ec6-49ba-85bb-0a6fe4abcb99 -->
# Finish Procedural Exec Handler (Multiplexer + Validation + Test Analysis)

### Scope

- Carry over the existing scope; exclude Future Work (port watcher, TMUX detachable).
- Complete only the remaining items and add a focused test analysis/porting plan.

### Progress

- Implemented serialized stdout/stderr + `WriteExit(code)` in `pkg/runner/multiplexer.go`.
- Wired non-TTY exit via multiplexer in `server/api/exec.go` before WS close.
- Analyzed exec-related tests and produced a shortlist to port.
- Implemented tests in `server/api/exec_new_test.go`:
- Basic non-TTY success
- Env propagation
- Stderr separation
- Large output drain
- TTY resize smoke
- Rapid-exit ordering (stdout before exit frame)
- Rapid-exit with large output (data fully delivered before exit)
- Concurrency/race (parallel sessions)
- Disconnect-cancels (client closes early)
- Executed `make test`; initial failures addressed.
- Added `RunContext()`/`Run()` compatibility helpers; renamed internal `Run()` to `Start()` and fixed call sites.
- Created `pkg/runner/validation_test.go`: context cancellation, large output drain (non-TTY & TTY), resize behavior tests all pass.
- Fixed `ptyReady` signaling for `newTTY` and `ttyMaster` cases to unblock `Resize()`.

### Testing Status

- `pkg/runner` validation tests: all pass.
- Remaining focus: runner-related server/api test failures only (not concerned with pkg/terminal or other server tests).

### Tests to Port Shortlist

- Basic non-TTY success: echo and expect `StreamStdout` then `StreamExit` in order (DONE)
- Env propagation: adapt `TestHandleExecWithEnvWithoutWrapper` for `HandleExecNew` (DONE)
- Stderr separation: assert `StreamStdout` and `StreamStderr` frames (DONE)
- Large output drain: adapt from `exec_large_output_test.go` (DONE)
- Rapid exit with large output: ensure exit frame is after data (DONE)
- Concurrency/race: parallel sessions (DONE)
- TTY resize: send resize; verify handling (DONE)
- Disconnect semantics: client closes early (DONE)

### Acceptance

- Multiplexer provides serialized stdout/stderr writes and `WriteExit(code)`.
- Non-TTY handler path writes exit signaling before WS close.
- All tests pass locally; manual validations behave as expected.
- Shortlist of tests-to-port is documented above.

### Running Tests

**Runner validation tests (can run locally without Docker):**
```bash
go test ./pkg/runner/... -run "TestCloseSemantics|TestLargeOutputDrain|TestResizeBehavior" -v -timeout=15s
```

**New exec handler tests (requires Docker):**
```bash
./scripts/run-tests-docker.sh -run TestExecNew ./server/api/...
```

**All runner tests (requires Docker):**
```bash
./scripts/run-tests-docker.sh ./pkg/runner/...
```

**Full test suite (requires Docker via make):**
```bash
make test
# Internally runs: ./scripts/run-tests-docker.sh
```

### To-dos

- [x] Run make test and address regressions (runner compile errors fixed; pkg/terminal & non-runner server tests out of scope)
- [x] Validate close semantics, large output drain, and resize behavior
- [x] Analyze server tests to identify exec-related cases to port
- [x] Produce shortlist mapping tests to new exec handler coverage
- [x] Implement remaining exec handler tests: rapid-exit ordering, concurrency/race, disconnect
- [ ] Disable server/ tests that hit exec_terminal handler (mark as skipped or comment out to avoid interference)
- [ ] Run new exec handler tests: `./scripts/run-tests-docker.sh -run TestExecNew ./server/api/...`