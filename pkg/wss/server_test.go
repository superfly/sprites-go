package wss

import (
	"context"
	"net/http"
	"net/http/httptest"
	"net/url"
	"strings"
	"testing"
	"time"

	gorillaws "github.com/gorilla/websocket"
)

func dialWS(t *testing.T, srv *httptest.Server, path string) *gorillaws.Conn {
	t.Helper()
	u, _ := url.Parse(srv.URL)
	u.Scheme = strings.ReplaceAll(u.Scheme, "http", "ws")
	// Support optional query in path arg
	if i := strings.IndexByte(path, '?'); i >= 0 {
		u.Path = path[:i]
		u.RawQuery = path[i+1:]
	} else {
		u.Path = path
	}
	conn, _, err := gorillaws.DefaultDialer.Dial(u.String(), nil)
	if err != nil {
		t.Fatalf("dial failed: %v", err)
	}
	return conn
}

func TestStartAndComplete(t *testing.T) {
	router := NewRouter()
	router.Handle("nop", func(ctx context.Context, c OpConn, args url.Values) error {
		return nil
	})
	s := &Server{Router: router}
	mux := http.NewServeMux()
	mux.HandleFunc("/control", func(w http.ResponseWriter, r *http.Request) {
		s.Handle(w, r)
	})
	ts := httptest.NewServer(mux)
	defer ts.Close()

	conn := dialWS(t, ts, "/control")
	defer conn.Close()

	// Send op.start
	startMsg := `control:{"type":"op.start","id":"1","op":"nop"}`
	if err := conn.WriteMessage(gorillaws.TextMessage, []byte(startMsg)); err != nil {
		t.Fatalf("write failed: %v", err)
	}

	// Expect ack then complete
	for i := 0; i < 2; i++ {
		mt, data, err := conn.ReadMessage()
		if err != nil {
			t.Fatalf("read failed: %v", err)
		}
		if mt != gorillaws.TextMessage || !strings.HasPrefix(string(data), "control:") {
			t.Fatalf("unexpected frame: %d %q", mt, string(data))
		}
	}
}

func TestBusy(t *testing.T) {
	router := NewRouter()
	router.Handle("sleep", func(ctx context.Context, c OpConn, args url.Values) error {
		select {
		case <-ctx.Done():
			return ctx.Err()
		case <-time.After(300 * time.Millisecond):
			return nil
		}
	})
	s := &Server{Router: router}
	mux := http.NewServeMux()
	mux.HandleFunc("/control", func(w http.ResponseWriter, r *http.Request) { s.Handle(w, r) })
	ts := httptest.NewServer(mux)
	defer ts.Close()

	conn := dialWS(t, ts, "/control")
	defer conn.Close()

	// Start long op
	_ = conn.WriteMessage(gorillaws.TextMessage, []byte(`control:{"type":"op.start","id":"1","op":"sleep"}`))

	// Immediately try to start again; expect error op.busy
	_ = conn.WriteMessage(gorillaws.TextMessage, []byte(`control:{"type":"op.start","id":"2","op":"sleep"}`))

	// Read at least two control frames
	var sawBusy bool
	deadline := time.Now().Add(1 * time.Second)
	for time.Now().Before(deadline) {
		mt, data, err := conn.ReadMessage()
		if err != nil {
			t.Fatalf("read failed: %v", err)
		}
		if mt == gorillaws.TextMessage && strings.HasPrefix(string(data), "control:") && strings.Contains(string(data), "op.busy") {
			sawBusy = true
			break
		}
	}
	if !sawBusy {
		t.Fatalf("expected op.busy error not received")
	}
}

func TestURLParamAutoStart(t *testing.T) {
	router := NewRouter()
	router.Handle("nop", func(ctx context.Context, c OpConn, args url.Values) error { return nil })
	s := &Server{Router: router}
	mux := http.NewServeMux()
	mux.HandleFunc("/control", func(w http.ResponseWriter, r *http.Request) { s.Handle(w, r) })
	ts := httptest.NewServer(mux)
	defer ts.Close()

	conn := dialWS(t, ts, "/control?op=nop")
	defer conn.Close()

	// Expect ack and complete without sending start
	for i := 0; i < 2; i++ {
		mt, data, err := conn.ReadMessage()
		if err != nil {
			t.Fatalf("read failed: %v", err)
		}
		if mt != gorillaws.TextMessage || !strings.HasPrefix(string(data), "control:") {
			t.Fatalf("unexpected frame: %d %q", mt, string(data))
		}
	}
}

func TestRejectFramesWhenNoOp(t *testing.T) {
	router := NewRouter()
	router.Handle("noop", func(ctx context.Context, c OpConn, args url.Values) error { return nil })
	s := &Server{Router: router}
	mux := http.NewServeMux()
	mux.HandleFunc("/control", func(w http.ResponseWriter, r *http.Request) { s.Handle(w, r) })
	ts := httptest.NewServer(mux)
	defer ts.Close()

	conn := dialWS(t, ts, "/control")
	defer conn.Close()

	// Send a data frame before starting any op; expect an op.error
	_ = conn.WriteMessage(gorillaws.TextMessage, []byte("hello-pre"))
	deadline := time.Now().Add(2 * time.Second)
	_ = conn.SetReadDeadline(deadline)
	sawError := false
	for !sawError {
		mt, data, err := conn.ReadMessage()
		if err != nil {
			t.Fatalf("read failed: %v", err)
		}
		if mt == gorillaws.TextMessage && strings.HasPrefix(string(data), "control:") && strings.Contains(string(data), "op.error") && strings.Contains(string(data), "op.not_active") {
			sawError = true
		}
	}
}

func TestMalformedControlFallsThrough(t *testing.T) {
	router := NewRouter()
	router.Handle("catch", func(ctx context.Context, c OpConn, args url.Values) error {
		// Expect to first receive a data frame after start
		mt, data, err := c.ReadMessage()
		if err != nil {
			return err
		}
		if mt != gorillaws.TextMessage || !strings.HasPrefix(string(data), "hello:") {
			t.Fatalf("expected text data after start, got %d %q", mt, string(data))
		}
		return nil
	})
	s := &Server{Router: router}
	mux := http.NewServeMux()
	mux.HandleFunc("/control", func(w http.ResponseWriter, r *http.Request) { s.Handle(w, r) })
	ts := httptest.NewServer(mux)
	defer ts.Close()

	conn := dialWS(t, ts, "/control")
	defer conn.Close()

	// Malformed control before any op should produce op.not_active error
	_ = conn.WriteMessage(gorillaws.TextMessage, []byte("control: not-json"))
	deadline := time.Now().Add(2 * time.Second)
	_ = conn.SetReadDeadline(deadline)
	sawNotActive := false
	for !sawNotActive {
		mt, data, err := conn.ReadMessage()
		if err != nil {
			t.Fatalf("read failed: %v", err)
		}
		if mt == gorillaws.TextMessage && strings.HasPrefix(string(data), "control:") && strings.Contains(string(data), "op.not_active") {
			sawNotActive = true
		}
	}

	// Now start the op and send a data text frame
	_ = conn.WriteMessage(gorillaws.TextMessage, []byte(`control:{"type":"op.start","id":"1","op":"catch"}`))
	_ = conn.WriteMessage(gorillaws.TextMessage, []byte("hello:data"))

	// Wait for op.complete
	deadline = time.Now().Add(2 * time.Second)
	_ = conn.SetReadDeadline(deadline)
	for {
		mt, data, err := conn.ReadMessage()
		if err != nil {
			return
		}
		if mt == gorillaws.TextMessage && strings.Contains(string(data), "op.complete") {
			return
		}
	}
}

func TestControlDuringActiveOpNotDelivered(t *testing.T) {
	router := NewRouter()
	router.Handle("two", func(ctx context.Context, c OpConn, args url.Values) error {
		// Expect two binary messages, control should be filtered
		for i := 0; i < 2; i++ {
			mt, data, err := c.ReadMessage()
			if err != nil {
				return err
			}
			if mt != gorillaws.BinaryMessage || string(data) != "data" {
				t.Fatalf("unexpected frame %d %q", mt, string(data))
			}
		}
		return nil
	})
	s := &Server{Router: router}
	mux := http.NewServeMux()
	mux.HandleFunc("/control", func(w http.ResponseWriter, r *http.Request) { s.Handle(w, r) })
	ts := httptest.NewServer(mux)
	defer ts.Close()

	conn := dialWS(t, ts, "/control")
	defer conn.Close()

	// Start op
	_ = conn.WriteMessage(gorillaws.TextMessage, []byte(`control:{"type":"op.start","id":"1","op":"two"}`))
	// Send binary, then a control (should be handled and not delivered), then another binary
	_ = conn.WriteMessage(gorillaws.BinaryMessage, []byte("data"))
	_ = conn.WriteMessage(gorillaws.TextMessage, []byte(`control:{"type":"noop"}`))
	_ = conn.WriteMessage(gorillaws.BinaryMessage, []byte("data"))

	// Wait for complete
	deadline := time.Now().Add(2 * time.Second)
	_ = conn.SetReadDeadline(deadline)
	for {
		mt, data, err := conn.ReadMessage()
		if err != nil {
			t.Fatalf("read failed: %v", err)
		}
		if mt == gorillaws.TextMessage && strings.Contains(string(data), "op.complete") {
			return
		}
	}
}

func TestSequentialOpsReuseConnection(t *testing.T) {
	router := NewRouter()
	// Handler reads one message then echoes it back with same message type
	router.Handle("bounce", func(ctx context.Context, c OpConn, args url.Values) error {
		mt, data, err := c.ReadMessage()
		if err != nil {
			return err
		}
		return c.WriteMessage(mt, data)
	})
	s := &Server{Router: router}
	mux := http.NewServeMux()
	mux.HandleFunc("/control", func(w http.ResponseWriter, r *http.Request) { s.Handle(w, r) })
	ts := httptest.NewServer(mux)
	defer ts.Close()

	conn := dialWS(t, ts, "/control")
	defer conn.Close()

	// Start op1
	_ = conn.WriteMessage(gorillaws.TextMessage, []byte(`control:{"type":"op.start","id":"1","op":"bounce"}`))
	// Send binary payload for op1
	payload1 := []byte("first-payload")
	_ = conn.WriteMessage(gorillaws.BinaryMessage, payload1)

	// Expect echo of op1 payload and then op.complete (dropped may be present but not required)
	sawEcho1 := false
	sawComplete1 := false
	deadline := time.Now().Add(3 * time.Second)
	_ = conn.SetReadDeadline(deadline)
	for !(sawEcho1 && sawComplete1) {
		mt, data, err := conn.ReadMessage()
		if err != nil {
			t.Fatalf("read failed: %v", err)
		}
		if mt == gorillaws.BinaryMessage && string(data) == string(payload1) {
			sawEcho1 = true
			continue
		}
		if mt == gorillaws.TextMessage && strings.HasPrefix(string(data), "control:") && strings.Contains(string(data), "op.complete") {
			sawComplete1 = true
			continue
		}
	}

	// Start op2, then send data, expect echo
	_ = conn.WriteMessage(gorillaws.TextMessage, []byte(`control:{"type":"op.start","id":"2","op":"bounce"}`))
	payload2 := []byte("second")
	_ = conn.WriteMessage(gorillaws.BinaryMessage, payload2)
	sawEcho2 := false
	deadline = time.Now().Add(3 * time.Second)
	_ = conn.SetReadDeadline(deadline)
	for !sawEcho2 {
		mt, data, err := conn.ReadMessage()
		if err != nil {
			t.Fatalf("read failed: %v", err)
		}
		if mt == gorillaws.BinaryMessage && string(data) == string(payload2) {
			sawEcho2 = true
			break
		}
	}

	// Ensure connection is still open by starting and completing a tiny op3 quickly
	_ = conn.WriteMessage(gorillaws.TextMessage, []byte(`control:{"type":"op.start","id":"3","op":"bounce"}`))
	_ = conn.WriteMessage(gorillaws.BinaryMessage, []byte("ok"))
	// Read a couple messages to confirm activity
	for i := 0; i < 2; i++ {
		if _, _, err := conn.ReadMessage(); err != nil {
			t.Fatalf("unexpected close: %v", err)
		}
	}
}
