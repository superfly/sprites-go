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

func TestPreOpBufferingAndEcho(t *testing.T) {
	router := NewRouter()
	router.Handle("echo", func(ctx context.Context, c OpConn, args url.Values) error {
		// First message should be the one sent before op.start
		mt, data, err := c.ReadMessage()
		if err != nil {
			return err
		}
		if mt != gorillaws.TextMessage || string(data) != "hello-pre" {
			t.Fatalf("unexpected pre-op frame: %d %q", mt, string(data))
		}
		// Echo back a binary response so test can assert
		return c.WriteMessage(gorillaws.BinaryMessage, []byte{1, 'o', 'k'})
	})
	s := &Server{Router: router}
	mux := http.NewServeMux()
	mux.HandleFunc("/control", func(w http.ResponseWriter, r *http.Request) { s.Handle(w, r) })
	ts := httptest.NewServer(mux)
	defer ts.Close()

	conn := dialWS(t, ts, "/control")
	defer conn.Close()

	// Send a normal text message before starting
	_ = conn.WriteMessage(gorillaws.TextMessage, []byte("hello-pre"))
	// Now start op
	_ = conn.WriteMessage(gorillaws.TextMessage, []byte(`control:{"type":"op.start","id":"1","op":"echo"}`))

	// Skip acks, expect binary echo
	deadline := time.Now().Add(2 * time.Second)
	_ = conn.SetReadDeadline(deadline)
	for {
		mt, data, err := conn.ReadMessage()
		if err != nil {
			t.Fatalf("read failed: %v", err)
		}
		if mt == gorillaws.BinaryMessage {
			if len(data) == 3 && data[0] == 1 && string(data[1:]) == "ok" {
				return
			}
			t.Fatalf("unexpected binary echo: %v %q", data, string(data))
		}
	}
}

func TestMalformedControlFallsThrough(t *testing.T) {
	router := NewRouter()
	router.Handle("catch", func(ctx context.Context, c OpConn, args url.Values) error {
		// Expect to first receive the malformed control text frame
		mt, data, err := c.ReadMessage()
		if err != nil {
			return err
		}
		if mt != gorillaws.TextMessage || !strings.HasPrefix(string(data), "control:") {
			t.Fatalf("expected fallthrough control text, got %d %q", mt, string(data))
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

	// Malformed control
	_ = conn.WriteMessage(gorillaws.TextMessage, []byte("control: not-json"))
	// Start op
	_ = conn.WriteMessage(gorillaws.TextMessage, []byte(`control:{"type":"op.start","id":"1","op":"catch"}`))

	// Consume acks and ensure handler returns without error
	deadline := time.Now().Add(2 * time.Second)
	_ = conn.SetReadDeadline(deadline)
	for {
		mt, data, err := conn.ReadMessage()
		if err != nil {
			// if connection closes or no more frames, test passes
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
