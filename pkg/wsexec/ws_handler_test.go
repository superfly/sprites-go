package wsexec

import (
	"net/http"
	"net/http/httptest"
	"net/url"
	"os/exec"
	"syscall"
	"testing"
	"time"

	creackpty "github.com/creack/pty"
	gorillaws "github.com/gorilla/websocket"
)

func newExecWSServer(t *testing.T, mk func() *exec.Cmd, opts ...HandlerOption) *httptest.Server {
	h := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := mk()
		Handler(cmd, opts...)(w, r)
	})
	return httptest.NewServer(h)
}

func dialWS(t *testing.T, ts *httptest.Server) *gorillaws.Conn {
	u, _ := url.Parse(ts.URL)
	u.Scheme = "ws"
	c, _, err := gorillaws.DefaultDialer.Dial(u.String(), nil)
	if err != nil {
		t.Fatalf("dial: %v", err)
	}
	return c
}

func waitUntilExit(t *testing.T, c *gorillaws.Conn) (sawOut, sawErr bool, exit byte) {
	deadline := time.Now().Add(5 * time.Second)
	_ = c.SetReadDeadline(deadline)
	for {
		_, data, err := c.ReadMessage()
		if err != nil {
			t.Fatalf("read: %v", err)
		}
		if len(data) == 0 {
			t.Fatalf("short msg")
		}
		sid := StreamID(data[0])
		switch sid {
		case StreamStdout:
			sawOut = true
		case StreamStderr:
			sawErr = true
		case StreamExit:
			if len(data) >= 2 {
				exit = data[1]
			}
			return
		}
	}
}

func TestFastNoStdin(t *testing.T) {
	ts := newExecWSServer(t, func() *exec.Cmd { return exec.Command("/bin/sh", "-c", "echo out; echo err 1>&2") })
	defer ts.Close()
	c := dialWS(t, ts)
	defer c.Close()
	sOut, sErr, _ := waitUntilExit(t, c)
	if !sOut || !sErr {
		t.Fatalf("missing streams out=%v err=%v", sOut, sErr)
	}
}

func TestNoOutputJustExit(t *testing.T) {
	ts := newExecWSServer(t, func() *exec.Cmd { return exec.Command("/bin/sh", "-c", "true") })
	defer ts.Close()
	c := dialWS(t, ts)
	defer c.Close()
	sOut, sErr, _ := waitUntilExit(t, c)
	if sOut || sErr {
		t.Fatalf("unexpected streams out=%v err=%v", sOut, sErr)
	}
}

func TestNonZeroExit(t *testing.T) {
	ts := newExecWSServer(t, func() *exec.Cmd { return exec.Command("/bin/sh", "-c", "exit 7") })
	defer ts.Close()
	c := dialWS(t, ts)
	defer c.Close()
	_, _, exitCode := waitUntilExit(t, c)
	if exitCode != 7 {
		t.Fatalf("expected exit code 7, got %d", exitCode)
	}
}

func TestExitCodeZero(t *testing.T) {
	ts := newExecWSServer(t, func() *exec.Cmd { return exec.Command("/bin/sh", "-c", "echo hello; exit 0") })
	defer ts.Close()
	c := dialWS(t, ts)
	defer c.Close()
	_, _, exitCode := waitUntilExit(t, c)
	if exitCode != 0 {
		t.Fatalf("expected exit code 0, got %d", exitCode)
	}
}

func TestExitCodeLarge(t *testing.T) {
	ts := newExecWSServer(t, func() *exec.Cmd { return exec.Command("/bin/sh", "-c", "exit 255") })
	defer ts.Close()
	c := dialWS(t, ts)
	defer c.Close()
	_, _, exitCode := waitUntilExit(t, c)
	if exitCode != 255 {
		t.Fatalf("expected exit code 255, got %d", exitCode)
	}
}

func TestExitCodeCommandNotFound(t *testing.T) {
	ts := newExecWSServer(t, func() *exec.Cmd { return exec.Command("/bin/sh", "-c", "/nonexistent/command") })
	defer ts.Close()
	c := dialWS(t, ts)
	defer c.Close()
	_, sErr, exitCode := waitUntilExit(t, c)
	// Command not found typically returns exit code 127
	if exitCode != 127 {
		t.Fatalf("expected exit code 127 for command not found, got %d", exitCode)
	}
	// Should have stderr output for command not found
	if !sErr {
		t.Fatalf("expected stderr output for command not found")
	}
}

func TestStdinWithEOF(t *testing.T) {
	ts := newExecWSServer(t, func() *exec.Cmd { return exec.Command("/bin/sh", "-c", "cat; echo 'DONE'") }, WithStdin())
	defer ts.Close()
	c := dialWS(t, ts)
	defer c.Close()
	// Send stdin data
	if err := c.WriteMessage(gorillaws.BinaryMessage, []byte("hello\n")); err != nil {
		t.Fatalf("write: %v", err)
	}
	// Send EOF signal using StreamStdinEOF
	if err := c.WriteMessage(gorillaws.BinaryMessage, []byte{byte(StreamStdinEOF)}); err != nil {
		t.Fatalf("write EOF: %v", err)
	}
	sOut, _, _ := waitUntilExit(t, c)
	if !sOut {
		t.Fatalf("missing stdout")
	}
}

func TestLargeStdout(t *testing.T) {
	// portable large output: print 100000 "x" via loop
	cmdLine := "i=0; while [ $i -lt 10000 ]; do printf xxxxxxxxxx; i=$((i+1)); done"
	ts := newExecWSServer(t, func() *exec.Cmd { return exec.Command("/bin/sh", "-c", cmdLine) })
	defer ts.Close()
	c := dialWS(t, ts)
	defer c.Close()
	sOut, _, _ := waitUntilExit(t, c)
	if !sOut {
		t.Fatalf("missing stdout")
	}
}

func TestStdinNotWrittenCommandStillExits(t *testing.T) {
	ts := newExecWSServer(t, func() *exec.Cmd { return exec.Command("/bin/sh", "-c", "sleep 0.1; echo done") })
	defer ts.Close()
	c := dialWS(t, ts)
	defer c.Close()
	sOut, _, _ := waitUntilExit(t, c)
	if !sOut {
		t.Fatalf("missing stdout")
	}
}

func TestStderrOnly(t *testing.T) {
	ts := newExecWSServer(t, func() *exec.Cmd { return exec.Command("/bin/sh", "-c", "echo err 1>&2") })
	defer ts.Close()
	c := dialWS(t, ts)
	defer c.Close()
	_, sErr, _ := waitUntilExit(t, c)
	if !sErr {
		t.Fatalf("missing stderr")
	}
}

func TestPTYLikeCommand(t *testing.T) {
	// Test a command that simulates PTY behavior by setting TERM
	ts := newExecWSServer(t, func() *exec.Cmd {
		cmd := exec.Command("/bin/sh", "-c", "echo $TERM; echo hello pty")
		cmd.Env = append(cmd.Env, "TERM=xterm-256color")
		return cmd
	})
	defer ts.Close()
	c := dialWS(t, ts)
	defer c.Close()
	sOut, _, _ := waitUntilExit(t, c)
	if !sOut {
		t.Fatalf("missing stdout from PTY-like command")
	}
}

func TestInteractiveCommandWithPrompt(t *testing.T) {
	// Test an interactive command that shows a prompt
	ts := newExecWSServer(t, func() *exec.Cmd {
		cmd := exec.Command("/bin/sh", "-c", "echo 'Enter your name:'; read -r name; echo 'Hello, $name!'")
		cmd.Env = append(cmd.Env, "TERM=xterm-256color")
		return cmd
	}, WithStdin())
	defer ts.Close()
	c := dialWS(t, ts)
	defer c.Close()

	// Wait a bit for the prompt to appear, then send input
	time.Sleep(100 * time.Millisecond)
	if err := c.WriteMessage(gorillaws.BinaryMessage, []byte("Alice\n")); err != nil {
		t.Fatalf("write: %v", err)
	}
	// Send EOF signal using StreamStdinEOF
	if err := c.WriteMessage(gorillaws.BinaryMessage, []byte{byte(StreamStdinEOF)}); err != nil {
		t.Fatalf("write EOF: %v", err)
	}

	sOut, _, _ := waitUntilExit(t, c)
	if !sOut {
		t.Fatalf("missing stdout from interactive command")
	}
}

func TestCommandWithTerminalColors(t *testing.T) {
	// Test a command that might produce colored output when TERM is set
	ts := newExecWSServer(t, func() *exec.Cmd {
		cmd := exec.Command("/bin/sh", "-c", "echo -e '\\033[32mGreen text\\033[0m'; echo -e '\\033[31mRed text\\033[0m'")
		cmd.Env = append(cmd.Env, "TERM=xterm-256color")
		return cmd
	})
	defer ts.Close()
	c := dialWS(t, ts)
	defer c.Close()

	sOut, _, _ := waitUntilExit(t, c)
	if !sOut {
		t.Fatalf("missing stdout from colored command")
	}
}

func TestRealPTYCommand(t *testing.T) {
	// Test with a real PTY
	ptmx, tty, err := creackpty.Open()
	if err != nil {
		t.Skip("PTY not supported on this system")
	}
	defer ptmx.Close()
	defer tty.Close()

	// Create command with PTY
	cmd := exec.Command("/bin/sh", "-c", "echo 'PTY test'; echo $TERM; echo 'Done'")
	cmd.Stdin = tty
	cmd.Stdout = tty
	cmd.Stderr = tty
	cmd.Env = append(cmd.Env, "TERM=xterm-256color")

	// Set up process group for PTY
	if cmd.SysProcAttr == nil {
		cmd.SysProcAttr = &syscall.SysProcAttr{}
	}
	cmd.SysProcAttr.Setsid = true
	cmd.SysProcAttr.Setctty = true

	// Create server with PTY
	ts := httptest.NewServer(Handler(cmd, WithPTY(ptmx)))
	defer ts.Close()
	c := dialWS(t, ts)
	defer c.Close()

	sOut, _, _ := waitUntilExit(t, c)
	if !sOut {
		t.Fatalf("missing stdout from PTY command")
	}
}

func TestInteractivePTYCommand(t *testing.T) {
	// Test interactive PTY command
	ptmx, tty, err := creackpty.Open()
	if err != nil {
		t.Skip("PTY not supported on this system")
	}
	defer ptmx.Close()
	defer tty.Close()

	// Create interactive command with PTY
	cmd := exec.Command("/bin/sh", "-c", "echo 'Enter your name:'; read -r name; echo 'Hello, $name!'")
	cmd.Stdin = tty
	cmd.Stdout = tty
	cmd.Stderr = tty
	cmd.Env = append(cmd.Env, "TERM=xterm-256color")

	// Set up process group for PTY
	if cmd.SysProcAttr == nil {
		cmd.SysProcAttr = &syscall.SysProcAttr{}
	}
	cmd.SysProcAttr.Setsid = true
	cmd.SysProcAttr.Setctty = true

	// Create server with PTY
	ts := httptest.NewServer(Handler(cmd, WithPTY(ptmx), WithStdin()))
	defer ts.Close()
	c := dialWS(t, ts)
	defer c.Close()

	// Wait a bit for the prompt to appear, then send input
	time.Sleep(100 * time.Millisecond)
	if err := c.WriteMessage(gorillaws.BinaryMessage, []byte("Alice\n")); err != nil {
		t.Fatalf("write: %v", err)
	}
	// Send EOF signal using StreamStdinEOF
	if err := c.WriteMessage(gorillaws.BinaryMessage, []byte{byte(StreamStdinEOF)}); err != nil {
		t.Fatalf("write EOF: %v", err)
	}

	sOut, _, _ := waitUntilExit(t, c)
	if !sOut {
		t.Fatalf("missing stdout from interactive PTY command")
	}
}

func TestPTYExitCodeZero(t *testing.T) {
	// Test PTY command with exit code 0
	ptmx, tty, err := creackpty.Open()
	if err != nil {
		t.Skip("PTY not supported on this system")
	}
	defer ptmx.Close()
	defer tty.Close()

	cmd := exec.Command("/bin/sh", "-c", "echo 'PTY exit test'; exit 0")
	cmd.Stdin = tty
	cmd.Stdout = tty
	cmd.Stderr = tty
	cmd.Env = append(cmd.Env, "TERM=xterm-256color")

	if cmd.SysProcAttr == nil {
		cmd.SysProcAttr = &syscall.SysProcAttr{}
	}
	cmd.SysProcAttr.Setsid = true
	cmd.SysProcAttr.Setctty = true

	ts := httptest.NewServer(Handler(cmd, WithPTY(ptmx)))
	defer ts.Close()
	c := dialWS(t, ts)
	defer c.Close()

	_, _, exitCode := waitUntilExit(t, c)
	if exitCode != 0 {
		t.Fatalf("expected PTY exit code 0, got %d", exitCode)
	}
}

func TestPTYExitCodeNonZero(t *testing.T) {
	// Test PTY command with non-zero exit code
	ptmx, tty, err := creackpty.Open()
	if err != nil {
		t.Skip("PTY not supported on this system")
	}
	defer ptmx.Close()
	defer tty.Close()

	cmd := exec.Command("/bin/sh", "-c", "echo 'PTY exit test'; exit 42")
	cmd.Stdin = tty
	cmd.Stdout = tty
	cmd.Stderr = tty
	cmd.Env = append(cmd.Env, "TERM=xterm-256color")

	if cmd.SysProcAttr == nil {
		cmd.SysProcAttr = &syscall.SysProcAttr{}
	}
	cmd.SysProcAttr.Setsid = true
	cmd.SysProcAttr.Setctty = true

	ts := httptest.NewServer(Handler(cmd, WithPTY(ptmx)))
	defer ts.Close()
	c := dialWS(t, ts)
	defer c.Close()

	_, _, exitCode := waitUntilExit(t, c)
	t.Logf("PTY exit code received: %d", exitCode)
	if exitCode != 42 {
		t.Fatalf("expected PTY exit code 42, got %d", exitCode)
	}
}

func TestPTYExitCodeWithStderr(t *testing.T) {
	// Test PTY command that writes to stderr and exits with non-zero code
	ptmx, tty, err := creackpty.Open()
	if err != nil {
		t.Skip("PTY not supported on this system")
	}
	defer ptmx.Close()
	defer tty.Close()

	cmd := exec.Command("/bin/sh", "-c", "echo 'stdout message'; echo 'stderr message' 1>&2; exit 99")
	cmd.Stdin = tty
	cmd.Stdout = tty
	cmd.Stderr = tty
	cmd.Env = append(cmd.Env, "TERM=xterm-256color")

	if cmd.SysProcAttr == nil {
		cmd.SysProcAttr = &syscall.SysProcAttr{}
	}
	cmd.SysProcAttr.Setsid = true
	cmd.SysProcAttr.Setctty = true

	ts := httptest.NewServer(Handler(cmd, WithPTY(ptmx)))
	defer ts.Close()
	c := dialWS(t, ts)
	defer c.Close()

	sOut, _, exitCode := waitUntilExit(t, c)
	t.Logf("PTY exit code with stderr: %d, saw stdout: %v", exitCode, sOut)
	if exitCode != 99 {
		t.Fatalf("expected PTY exit code 99, got %d", exitCode)
	}
	if !sOut {
		t.Fatalf("expected stdout output from PTY command")
	}
}
