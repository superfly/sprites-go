## pkg/cmd: Robust command IO + PTY runner (tests-first)

### Goals
- Procedural, race-free command execution with strict IO/PTY semantics.
- Exit code returned only after stdout/stderr (or PTY) are fully drained.
- Never use StdoutPipe/StderrPipe. Use StdinPipe only for a cancellable stdin loop.
- Channel-based synchronization only (WaitGroups OK). Prefer unbuffered channels unless tests justify otherwise.

### Public API (initial)
- Type: `Runner` with `Run(ctx context.Context, cmd *exec.Cmd, opts ...Option) (exitCode int, err error)`
- Options:
  - `WithStdin(r io.Reader)`
  - `WithStdout(w io.Writer)`
  - `WithStderr(w io.Writer)`
  - `WithNewTTY()`  // allocate a new PTY; merges stdout/stderr
  - `WithTTY(tty *os.File)` // use caller-provided PTY master; assumes slave is wired to the child externally
  - `WithWaitTTY(fn func(ctx context.Context) (*os.File, error))` // after Start, callback returns PTY master (e.g., fd-pass via socket); source-agnostic
- Validation (error on):
  - any combination of `WithNewTTY()` with `WithTTY(...)` or `WithWaitTTY(...)`
  - `WithTTY(...)` with `WithWaitTTY(...)`
  - any TTY option with `WithStderr(...)` (TTY merges streams)
  - missing stdout writer in all modes

### Execution semantics (non-TTY)
- Set `cmd.Stdout = providedStdoutWriter` and `cmd.Stderr = providedStderrWriter` directly (no extra goroutines/pipes introduced by us).
- Stdin: ALWAYS run a dedicated stdin loop using `cmd.StdinPipe()` to enable deterministic cancellation and EOF forwarding (close the pipe on EOF/cancel).
- Start the command; start the stdin loop; wait for `cmd.Wait()`; then return exit code (which implies stdout/stderr draining completed when using direct writers).
- Process group: setpgid=true so we can kill the group on cancel.

### Execution semantics (TTY)
- `WithNewTTY()`: open `(master, slave)` via `creack/pty`. Assign slave to `cmd.Stdin/Stdout/Stderr`; set `SysProcAttr{Setsid: true, Setctty: true}`; after `cmd.Start()`, close `slave` in parent.
- `WithTTY(master)`: use provided master; assume slave wired to the child by caller; after `Start()`, continue as normal.
- `WithWaitTTY(fn)`: after `Start()`, call `fn(ctx)` to obtain PTY master (e.g., via fd-pass over Unix socket); proceed as with master.
- IO:
  - Single reader: `io.Copy(stdoutWriter, master)` (merged stream). No stderr writer in TTY.
  - Optional stdin: single writer loop `io.Copy(master, stdinReader)`; do not close master from the stdin goroutine.
- Lifecycle: wait on `cmd.Wait()`; then wait for the PTY read loop to finish (master EOF) before returning exit code.

### Ordering guarantees
- Non-TTY: rely on `os/exec` copiers to deliver all bytes to our direct writers before `Wait()` returns; we add no buffering.
- TTY: return only after PTY reader finishes (master reaches EOF after child exit/slave close).

### Internal sync model
- Unbuffered `done` channels and `sync.WaitGroup` to gate continuation; no mutexes.
- Use `select` on closed channels to progress, per rules.

### Tests-first: matrix + stress
- Force `runtime.GOMAXPROCS(1)` in stress tests to surface races.
- Run large N short-lived commands concurrently with no explicit parallelism limiting.
- Verify: all outputs complete; stdin fully consumed; exit observed only after final byte delivered.

### Test cases
- Non-TTY basic: echo to stdout/stderr; confirm bytes and exit code.
- Non-TTY large output: MB-scale stdout and stderr; completeness checks.
- Non-TTY stdin: `cat`/`tr` with input; full roundtrip.
- Non-TTY stdin early-close: `head -n1` style; ensure stdin loop terminates without deadlock.
- TTY basic: merged output correctness (normalize CRLF) and exit codes.
- TTY large: spam output; verify completeness and ordering.
- TTY stdin: interactive `cat` under PTY; correct echo; EOF handling; slave-close determinism.
- `WithWaitTTY` success and error paths: stub provider returns a PTY master, plus concurrency variants.
- Concurrency stress: GOMAXPROCS(1), unlimited goroutines.
- TCP bridge tests: use net.Conn as stdin/stdout and (for TTY) merged stream to validate network-backed IO.
- Options conflict tests.

### Files added
- `pkg/cmd/runner.go` (public API, options, validation)
- `pkg/cmd/run_non_tty.go` (non-TTY path with direct writers and cancellable stdin loop)
- `pkg/cmd/run_tty_unix.go` (TTY path; Setsid/Setctty; slave close; merged IO)
- `pkg/cmd/tty_helpers_unix.go` (placeholder for future helpers like resize)
- `pkg/cmd/errors.go` (exported error vars)
- `pkg/cmd/readpump.go` (StartReadPump for robust stdin copying)
- Tests under `pkg/cmd/`: non-TTY, TTY, concurrency, large output, stdin early-close, TCP bridge, WaitTTY success/error, and stress tests

### Reuse and alignment
- Use proven PTY patterns (`Setsid+Setctty` and closing the slave after `Start()`).
- Avoid `StdoutPipe/StderrPipe`; rely on direct writers to minimize buffering and races.

### Out-of-scope (initial)
- Windows support.
- Advanced signal proxying beyond process-group kill on cancel.
