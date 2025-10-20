package api

import (
	"context"
	"encoding/json"
	"io"
	"log/slog"
	"net"
	"net/url"
	"strconv"
	"testing"
	"time"

	gorillaws "github.com/gorilla/websocket"
	"github.com/superfly/sprite-env/pkg/tap"
)

// TestControlProxyEcho verifies the 'proxy' control op establishes a TCP tunnel
// and forwards binary data bidirectionally.
func TestControlProxyEcho(t *testing.T) {
	// Start a simple TCP echo server on 127.0.0.1:0
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatalf("failed to start echo server: %v", err)
	}
	defer ln.Close()

	echoDone := make(chan struct{})
	go func() {
		defer close(echoDone)
		for {
			conn, err := ln.Accept()
			if err != nil {
				return
			}
			go func(c net.Conn) {
				defer c.Close()
				_, _ = io.Copy(c, c)
			}(conn)
		}
	}()

	// Build handlers (no system needed for proxy)
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	h := NewHandlers(ctx, nil, HandlerConfig{})

	// Start control API server
	ts := newControlAPIServer(t, h)
	defer ts.Close()

	// Build ws:// URL to /v1/sprites/foo/control
	u, _ := url.Parse(ts.URL)
	u.Scheme = "ws"
	u.Path = "/v1/sprites/foo/control"

	// Connect websocket
	c, _, err := gorillaws.DefaultDialer.Dial(u.String(), nil)
	if err != nil {
		t.Fatalf("ws dial failed: %v", err)
	}
	defer c.Close()

	// Start proxy op with host and port args over control
	port := ln.Addr().(*net.TCPAddr).Port
	env := map[string]any{
		"type": "op.start",
		"op":   "proxy",
		"args": map[string]any{
			"host": "127.0.0.1",
			"port": strconv.Itoa(port),
		},
	}
	payload, _ := json.Marshal(env)
	if err := c.WriteMessage(gorillaws.TextMessage, append([]byte("control:"), payload...)); err != nil {
		t.Fatalf("send control op.start failed: %v", err)
	}

	// Expect a connected message (non-control text JSON)
	_ = c.SetReadDeadline(time.Now().Add(3 * time.Second))
	for {
		mt, data, err := c.ReadMessage()
		if err != nil {
			t.Fatalf("read message failed: %v", err)
		}
		if mt != gorillaws.TextMessage {
			continue
		}
		if len(data) >= len("control:") && string(data[:len("control:")]) == "control:" {
			// skip control frames
			continue
		}
		var msg map[string]any
		if err := json.Unmarshal(data, &msg); err == nil {
			if msg["status"] == "connected" {
				break
			}
		}
	}

	// Send binary payload and expect echo
	send := []byte("hello over proxy")
	if err := c.WriteMessage(gorillaws.BinaryMessage, send); err != nil {
		t.Fatalf("write binary failed: %v", err)
	}
	mt, recv, err := c.ReadMessage()
	if err != nil {
		t.Fatalf("read echoed binary failed: %v", err)
	}
	if mt != gorillaws.BinaryMessage {
		t.Fatalf("expected binary echo, got type %d", mt)
	}
	if string(recv) != string(send) {
		t.Fatalf("unexpected echo: got %q want %q", string(recv), string(send))
	}
}
