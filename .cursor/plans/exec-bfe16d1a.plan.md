<!-- bfe16d1a-9224-40e0-89de-11367bc5ba9e 8f619347-25b2-47ac-b7dc-26712f263a84 -->
# Exec Handler + Runner Design Refinement

### Goals

- **No output loss on close**: deterministic ordering and draining when client disconnects or process exits.
- **Procedural handler**: straight-line flow; no handler-managed I/O loops or goroutines.
- **I/O handled for us**: All copying/loops live inside `pkg/runner` and tiny adapters.

### Why no errgroup

- We don't wait on a websocket monitor. **Adapter read/write errors** propagate into runner I/O copies and cause completion.
- The handler uses a simple sequence: `Run()` (async start) → `PID()` (block until set) → `Wait()` (block until exit). No extra goroutines in handler.

### Key design changes

- **Async `Run()`**: Starts the process and returns immediately. Returns an error only if `cmd.Start()` failed (process never started).
- **`Wait()`**: Blocks until the process exits, ensuring stdout/stderr drains before returning and exit code is stored.
- **Blocking `PID()` via `pidReady`**: Runner exposes `PID()` that blocks until PID is set right after successful `cmd.Start()`. Uses the construction context internally.
- **No sleeps/polling**: Eliminate all `time.Sleep(...)` and handler polling/monitor loops.
- **Write serialization + graceful close**: `wsWriter` serializes writes; after `Wait` returns, write exit frame (non-TTY), then WebSocket close control, then `Close()`.
- **TTY resizes without handler goroutines**: `wsReader.Read` handles text control (resize) while providing binary stdin. If `stdin=false`, copy to `io.Discard` so control still flows.
- **Keep protocol local**: Stream IDs/constants live in `pkg/runner`; do not share with SDKs.

### Proposed handler flow (`server/api/exec.go`)

1. Upgrade WebSocket; optionally set write deadlines.
2. Build `exec.Cmd` (path, args, env, dir); pass through `system.WrapContainer(cmd, tty)`.
3. Create adapters:

- `wsReader` (`io.Reader`) yielding binary payloads; interprets text control (resize → `runner.Resize`).
- `wsWriter` (`io.Writer`) with a mutex and optional per-write deadline.
- Non-TTY: wrap `wsWriter` in `runner.NewMultiplexedWriter` for stdout/stderr/exit.

4. Construct runner with context: `run := runner.New(ctx, finalCmd, opts...)`.
5. Start: `if err := run.Run(); err != nil { /* start failed */ return }` (returns immediately on success).
6. `pid := run.PID()`; register with `portWatcher`.
7. `waitErr := run.Wait()`.
8. `exitCode := run.ExitCode()`; in non-TTY write `Exit` frame via mux; then close WebSocket.

### Runner responsibilities (`pkg/runner`)

- Public API: `New(ctx, *exec.Cmd, ...Option) *Runner`, `Run() error` (async start), `Wait() error` (blocking), `ExitCode() int`, `PID() int` (blocks until ready).
- Internals:
- After successful `cmd.Start()`, set PID and `close(pidReady)`; spawn minimal I/O copy goroutines; begin wait coordination.
- `Wait()` waits on `cmd.Wait()` or context cancellation, then waits for all I/O goroutines to finish before returning; extracts and stores exit code.
- TTY specifics:
- Allocate PTY and wire stdin/stdout through master end.
- If TTY `stdin=false`, run `io.Copy(wsReader → io.Discard)` to consume control messages.

### Connection closure semantics

- No websocket monitor in handler. Closure is detected by:
- `wsReader.Read` error when client closes (stdin copy ends).
- `wsWriter.Write` error when client closed during output (stdout/stderr copy ends).
- After `Wait` returns, if socket still open, write exit frame (non-TTY), then close handshake.

### Protocol and adapters

- Keep stream IDs in `pkg/runner` only: `Stdin=0, Stdout=1, Stderr=2, Exit=3, StdinEOF=4`.
- `MultiplexedWriter` does synchronous prefix-and-write only; no background goroutines.

### Items to remove (sleeps/loops)

- `time.Sleep(10ms)` previously used before reading PID.
- `wsMonitor.Wait` polling/loop.
- Any handler-level periodic checks. Adapter-internal `Read` loops are expected for `io.Reader`.

### Minimal file changes

- `server/api/exec.go`: procedural sequence using `Run` (async), `PID()`, `Wait()`; remove `wsMonitor` and sleeps; write exit then close.
- `pkg/runner/runner.go`: add `pidReady`; implement `Run` (start + return), `Wait` (block + drain I/O), `PID()` (block until set), `ExitCode()` storage.
- `pkg/runner/run_tty_unix.go` / `run_non_tty.go`: ensure `pidReady` close occurs post-`cmd.Start()`; support control-only stdin in TTY.
- `pkg/runner/multiplexer.go`: ensure sync-only writes; `WriteExit(code)` helper.
- `pkg/container/wrap.go` and `server/system/wrap.go`: unchanged.

### Edge cases to validate

- Client closes mid-output → write errors propagate; `Wait` returns; no panics; process killed on context cancel if needed.
- Large stdout at exit → output drains before `Wait` returns; exit frame written if possible.
- TTY resize with no stdin data → resizes applied via control-only path.
- Containerized TTY with `WithWaitTTY(getPTY)` path.

### To-dos (ordered)

- [ ] Implement `pidReady` and `PID()` in `pkg/runner`; close `pidReady` after `cmd.Start()`.
- [ ] Implement async `Run()` and blocking `Wait()`; ensure runner drains I/O and stores exit code.
- [ ] Update TTY/non-TTY run paths to honor control-only stdin when needed.
- [ ] Make handler procedural: build cmd, adapters; call `Run()`; get `PID()`; register PID; `Wait()`; write exit (non-TTY); close WebSocket.
- [ ] Remove any `time.Sleep` and delete `wsMonitor` usage.
- [ ] Keep stream ID constants in `pkg/runner` only; verify mux writes are synchronous.

### To-dos

- [ ] Make exec handler procedural: Start, register PID, Wait, write exit, close
- [ ] Add Start/Wait API to runner; keep Run convenience
- [ ] Remove websocket monitor from handler; rely on read/write errors
- [ ] Support TTY control-only stdin path (consume to discard)