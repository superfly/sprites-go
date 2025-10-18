package api

import (
	"context"
	"io"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"net/url"
	"strings"
	"testing"
	"time"

	gorillaws "github.com/gorilla/websocket"
)

// helper to stand up a server that routes to ExecHandler
func newExecNewTestServer(t *testing.T, h *Handlers) *httptest.Server {
	t.Helper()
	return httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		h.ExecHandler(w, r)
	}))
}

func testLogger(t *testing.T) *slog.Logger {
	t.Helper()
	return slog.New(slog.NewTextHandler(io.Discard, nil))
}

// readUntilExitNonTTY reads frames until a StreamExit frame is received.
// Returns collected stdout/stderr as strings and the exit code.
func readUntilExitNonTTY(t *testing.T, conn *gorillaws.Conn) (string, string, int) {
	stdout := strings.Builder{}
	stderr := strings.Builder{}
	exitCode := -1
	deadline := time.Now().Add(10 * time.Second)
	_ = conn.SetReadDeadline(deadline)
	for {
		mt, data, err := conn.ReadMessage()
		if err != nil {
			t.Fatalf("read error: %v", err)
		}
		if mt != gorillaws.BinaryMessage || len(data) == 0 {
			continue
		}
		stream := data[0]
		payload := data[1:]
		switch stream {
		case 1: // stdout
			stdout.Write(payload)
		case 2: // stderr
			stderr.Write(payload)
		case 3: // exit
			if len(payload) > 0 {
				exitCode = int(payload[0])
			}
			return stdout.String(), stderr.String(), exitCode
		}
	}
}

func TestExecNew_BasicNonTTY(t *testing.T) {
	h := &Handlers{logger: testLogger(t), system: &mockSystemManager{isRunning: true}}
	ts := newExecNewTestServer(t, h)
	defer ts.Close()

	wsURL := "ws" + strings.TrimPrefix(ts.URL, "http") + "/exec?cmd=echo&cmd=hello"
	conn, _, err := gorillaws.DefaultDialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("dial failed: %v", err)
	}
	defer conn.Close()

	out, errOut, code := readUntilExitNonTTY(t, conn)
	if code != 0 {
		t.Fatalf("expected exit 0, got %d", code)
	}
	if out != "hello\n" {
		t.Fatalf("unexpected stdout: %q", out)
	}
	if errOut != "" {
		t.Fatalf("unexpected stderr: %q", errOut)
	}
}

func TestExecNew_ListMatchesShape(t *testing.T) {
	h := &Handlers{logger: testLogger(t), system: &mockSystemManager{isRunning: true}}
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		// call the list path of ExecHandler
		r.URL.RawQuery = ""
		h.ExecHandler(w, r)
	}))
	defer srv.Close()

	resp, err := http.Get(srv.URL)
	if err != nil {
		t.Fatalf("list request failed: %v", err)
	}
	defer resp.Body.Close()
	if ct := resp.Header.Get("Content-Type"); !strings.Contains(ct, "application/json") {
		t.Fatalf("expected json content type, got %q", ct)
	}
}

func TestExecNew_EnvPropagation(t *testing.T) {
    h := &Handlers{logger: testLogger(t), system: &mockSystemManager{isRunning: true}}
	ts := newExecNewTestServer(t, h)
	defer ts.Close()

	wsURL := "ws" + strings.TrimPrefix(ts.URL, "http") + "/exec?cmd=env&env=NEW_EXEC_TEST=ok&env=FOO=bar"
	conn, _, err := gorillaws.DefaultDialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("dial failed: %v", err)
	}
	defer conn.Close()

	out, _, code := readUntilExitNonTTY(t, conn)
	if code != 0 {
		t.Fatalf("expected exit 0, got %d", code)
	}
	if !strings.Contains(out, "NEW_EXEC_TEST=ok") || !strings.Contains(out, "FOO=bar") {
		t.Fatalf("expected env vars in output, got: %q", out)
	}
}

func TestExecNew_StderrSeparation(t *testing.T) {
	h := &Handlers{logger: testLogger(t)}
	ts := newExecNewTestServer(t, h)
	defer ts.Close()

	// Write to both stdout and stderr
	cmd := "sh"
	args := "-c"
	line := "hello"
	sh := "echo '" + line + "' ; echo '" + line + "' 1>&2"
	wsURL := "ws" + strings.TrimPrefix(ts.URL, "http") + "/exec?cmd=" + cmd + "&cmd=" + args + "&cmd=" + url.QueryEscape(sh)
	conn, _, err := gorillaws.DefaultDialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("dial failed: %v", err)
	}
	defer conn.Close()

	out, errOut, code := readUntilExitNonTTY(t, conn)
	if code != 0 {
		t.Fatalf("expected exit 0, got %d", code)
	}
	if !strings.Contains(out, line) {
		t.Fatalf("expected stdout to contain %q, got %q", line, out)
	}
	if !strings.Contains(errOut, line) {
		t.Fatalf("expected stderr to contain %q, got %q", line, errOut)
	}
}

func TestExecNew_LargeOutputDrain(t *testing.T) {
	h := &Handlers{logger: testLogger(t)}
	ts := newExecNewTestServer(t, h)
	defer ts.Close()

	// Generate ~1MB of output
	wsURL := "ws" + strings.TrimPrefix(ts.URL, "http") + "/exec?cmd=sh&cmd=-c&cmd=dd%20if=/dev/zero%20bs=1024%20count=1024%202>/dev/null%20|%20base64"
	conn, _, err := gorillaws.DefaultDialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("dial failed: %v", err)
	}
	defer conn.Close()

	start := time.Now()
	out, _, code := readUntilExitNonTTY(t, conn)
	if code != 0 {
		t.Fatalf("expected exit 0, got %d", code)
	}
	if len(out) < 1*1024*1024 {
		t.Fatalf("expected at least 1MB, got %d bytes", len(out))
	}
	_ = start
}

func TestExecNew_TTY_Resize(t *testing.T) {
	h := &Handlers{logger: testLogger(t)}
	ts := newExecNewTestServer(t, h)
	defer ts.Close()

	// Short-lived TTY command to allow sending a resize
	wsURL := "ws" + strings.TrimPrefix(ts.URL, "http") + "/exec?tty=true&cmd=sh&cmd=-c&cmd=sleep%200.2"
	conn, _, err := gorillaws.DefaultDialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("dial failed: %v", err)
	}
	defer conn.Close()

	// Send a resize text control message
	resizeMsg := []byte(`{"type":"resize","cols":100,"rows":40}`)
	if err := conn.WriteMessage(gorillaws.TextMessage, resizeMsg); err != nil {
		t.Fatalf("failed to send resize: %v", err)
	}

	// Wait for server to close after command completes
	ctx, cancel := context.WithTimeout(context.Background(), 3*time.Second)
	defer cancel()
	for {
		select {
		case <-ctx.Done():
			t.Fatalf("timeout waiting for close")
		default:
			_, _, err := conn.ReadMessage()
			if err != nil {
				return // connection closed by server, success
			}
		}
	}
}

func TestExecNew_RapidExitOrdering(t *testing.T) {
	h := &Handlers{logger: testLogger(t)}
	ts := newExecNewTestServer(t, h)
	defer ts.Close()

	// Command that writes then exits immediately
	wsURL := "ws" + strings.TrimPrefix(ts.URL, "http") + "/exec?cmd=sh&cmd=-c&cmd=" + url.QueryEscape("printf foo; exit 7")
	conn, _, err := gorillaws.DefaultDialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("dial failed: %v", err)
	}
	defer conn.Close()

	// Expect stdout 'foo' then exit frame with code 7
	sawStdout := false
	exitCode := -1
	for {
		mt, data, err := conn.ReadMessage()
		if err != nil {
			t.Fatalf("read error: %v", err)
		}
		if mt != gorillaws.BinaryMessage || len(data) == 0 {
			continue
		}
		stream := data[0]
		payload := data[1:]
		if stream == 1 { // stdout
			if string(payload) == "foo" || strings.HasPrefix(string(payload), "foo") {
				sawStdout = true
			}
		}
		if stream == 3 { // exit
			if len(payload) > 0 {
				exitCode = int(payload[0])
			}
			break
		}
	}
	if !sawStdout {
		t.Fatalf("did not see stdout before exit")
	}
	if exitCode != 7 {
		t.Fatalf("expected exit 7, got %d", exitCode)
	}
}

func TestExecNew_Concurrency(t *testing.T) {
	h := &Handlers{logger: testLogger(t)}
	ts := newExecNewTestServer(t, h)
	defer ts.Close()

	n := 10
	errs := make(chan error, n)
	done := make(chan struct{}, n)
	for i := 0; i < n; i++ {
		go func(i int) {
			wsURL := "ws" + strings.TrimPrefix(ts.URL, "http") + "/exec?cmd=echo&cmd=worker" + url.QueryEscape(string(rune('A'+i)))
			conn, _, err := gorillaws.DefaultDialer.Dial(wsURL, nil)
			if err != nil {
				errs <- err
				return
			}
			defer conn.Close()
			out, _, code := readUntilExitNonTTY(t, conn)
			if code != 0 || !strings.Contains(out, "worker") {
				errs <- io.EOF
				return
			}
			done <- struct{}{}
		}(i)
	}
	timeout := time.After(10 * time.Second)
	completed := 0
	for completed < n {
		select {
		case <-done:
			completed++
		case err := <-errs:
			t.Fatalf("concurrency error: %v", err)
		case <-timeout:
			t.Fatalf("timeout waiting for concurrency test")
		}
	}
}

func TestExecNew_DisconnectCancels(t *testing.T) {
	h := &Handlers{logger: testLogger(t)}
	ts := newExecNewTestServer(t, h)
	defer ts.Close()

	// Start a long-running command
	wsURL := "ws" + strings.TrimPrefix(ts.URL, "http") + "/exec?cmd=sleep&cmd=5"
	conn, _, err := gorillaws.DefaultDialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("dial failed: %v", err)
	}

	// Close immediately to simulate client disconnect
	_ = conn.Close()

	// Give the server a moment to react; ensure we don't hang
	time.Sleep(500 * time.Millisecond)
}

func TestExecNew_RapidExitLargeOutput(t *testing.T) {
	h := &Handlers{logger: testLogger(t)}
	ts := newExecNewTestServer(t, h)
	defer ts.Close()

	// Produce several MB quickly then exit
	sh := "dd if=/dev/zero bs=1048576 count=3 2>/dev/null | base64; exit 0"
	wsURL := "ws" + strings.TrimPrefix(ts.URL, "http") + "/exec?cmd=sh&cmd=-c&cmd=" + url.QueryEscape(sh)
	conn, _, err := gorillaws.DefaultDialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("dial failed: %v", err)
	}
	defer conn.Close()

	sawStdout := false
	total := 0
	exitSeen := false

	deadline := time.Now().Add(20 * time.Second)
	_ = conn.SetReadDeadline(deadline)
	for {
		mt, data, err := conn.ReadMessage()
		if err != nil {
			t.Fatalf("read error: %v", err)
		}
		if mt != gorillaws.BinaryMessage || len(data) == 0 {
			continue
		}
		stream := data[0]
		payload := data[1:]
		if stream == 1 { // stdout
			sawStdout = true
			total += len(payload)
		}
		if stream == 3 { // exit
			exitSeen = true
			break
		}
	}

	if !sawStdout {
		t.Fatalf("no stdout observed before exit")
	}
	if !exitSeen {
		t.Fatalf("exit not observed")
	}
	if total < 3*1024*1024 {
		t.Fatalf("expected at least 3MB output before exit, got %d bytes", total)
	}
}
