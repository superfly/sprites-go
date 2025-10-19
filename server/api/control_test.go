package api

import (
	"io"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
	"time"

	gorillaws "github.com/gorilla/websocket"
)

func newControlTestServer(t *testing.T, h *Handlers) *httptest.Server {
	t.Helper()
	return httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		h.HandleControl(w, r)
	}))
}

func TestControl_ExecNonTTY(t *testing.T) {
	h := &Handlers{logger: testLogger(t), system: &mockSystemManager{isRunning: true}}
	ts := newControlTestServer(t, h)
	defer ts.Close()

	// Connect and start exec via control message
	wsURL := "ws" + strings.TrimPrefix(ts.URL, "http") + "/v1/sprites/foo/control"
	conn, _, err := gorillaws.DefaultDialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("dial failed: %v", err)
	}
	defer conn.Close()

	// Start an echo command using args similar to /exec query params
	ctrl := `control:{"type":"op.start","id":"1","op":"exec","args":{"cmd":["echo","hello"],"path":"echo"}}`
	if err := conn.WriteMessage(gorillaws.TextMessage, []byte(ctrl)); err != nil {
		t.Fatalf("send control failed: %v", err)
	}

	// Expect ack and then stream frames ending with exit
	// Skip control ack frames until we see binary frames
	deadline := time.Now().Add(10 * time.Second)
	_ = conn.SetReadDeadline(deadline)
	var stdout strings.Builder
	var exitCode = -1
	for {
		mt, data, err := conn.ReadMessage()
		if err != nil {
			t.Fatalf("read failed: %v", err)
		}
		if mt == gorillaws.TextMessage && strings.HasPrefix(string(data), "control:") {
			continue
		}
		if mt != gorillaws.BinaryMessage || len(data) == 0 {
			continue
		}
		stream := data[0]
		payload := data[1:]
		if stream == 1 {
			stdout.Write(payload)
		}
		if stream == 3 {
			if len(payload) > 0 {
				exitCode = int(payload[0])
			}
			break
		}
	}
	if exitCode != 0 {
		t.Fatalf("expected exit 0, got %d", exitCode)
	}
	if strings.TrimSpace(stdout.String()) != "hello" {
		t.Fatalf("unexpected stdout: %q", stdout.String())
	}
}

func TestControl_Busy(t *testing.T) {
	h := &Handlers{logger: slog.New(slog.NewTextHandler(io.Discard, nil))}
	ts := newControlTestServer(t, h)
	defer ts.Close()

	wsURL := "ws" + strings.TrimPrefix(ts.URL, "http") + "/v1/sprites/foo/control"
	conn, _, err := gorillaws.DefaultDialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("dial failed: %v", err)
	}
	defer conn.Close()

	// Start a sleep via exec
	start := `control:{"type":"op.start","id":"1","op":"exec","args":{"cmd":["sleep","1"],"path":"sleep"}}`
	_ = conn.WriteMessage(gorillaws.TextMessage, []byte(start))

	// Attempt another op start while busy
	again := `control:{"type":"op.start","id":"2","op":"exec","args":{"cmd":["echo","ok"],"path":"echo"}}`
	_ = conn.WriteMessage(gorillaws.TextMessage, []byte(again))

	// Expect an op.error with op.busy
	sawBusy := false
	deadline := time.Now().Add(2 * time.Second)
	_ = conn.SetReadDeadline(deadline)
	for !sawBusy {
		mt, data, err := conn.ReadMessage()
		if err != nil {
			t.Fatalf("read failed: %v", err)
		}
		if mt == gorillaws.TextMessage && strings.HasPrefix(string(data), "control:") && strings.Contains(string(data), "op.busy") {
			sawBusy = true
		}
	}
}

func TestControl_StdinNonTTY(t *testing.T) {
	h := &Handlers{logger: testLogger(t), system: &mockSystemManager{isRunning: true}}
	ts := newControlTestServer(t, h)
	defer ts.Close()

	wsURL := "ws" + strings.TrimPrefix(ts.URL, "http") + "/v1/sprites/foo/control"
	conn, _, err := gorillaws.DefaultDialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("dial failed: %v", err)
	}
	defer conn.Close()

	// Start a non-TTY exec that reads exactly 4 bytes from stdin and echoes them
	ctrl := `control:{"type":"op.start","id":"1","op":"exec","args":{"path":"dd","cmd":["dd","bs=4","count=1","status=none"],"stdin":"true"}}`
	if err := conn.WriteMessage(gorillaws.TextMessage, []byte(ctrl)); err != nil {
		t.Fatalf("send control failed: %v", err)
	}

	// Send 4 bytes of stdin
	in := []byte("ABCD")
	if err := conn.WriteMessage(gorillaws.BinaryMessage, in); err != nil {
		t.Fatalf("send stdin failed: %v", err)
	}

	// Read until exit and verify stdout contains the bytes we sent
	out, _, code := readUntilExitNonTTY(t, conn)
	if code != 0 {
		t.Fatalf("expected exit 0, got %d", code)
	}
	if !strings.Contains(out, "ABCD") {
		t.Fatalf("expected stdout to contain input bytes, got %q", out)
	}
}
