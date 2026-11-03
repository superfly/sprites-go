package sprites

import (
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
	"time"

	"github.com/gorilla/websocket"
)

// TestWriteLoopBoundsWritesOnAStalledPeer checks that a peer which stops
// reading cannot wedge the write loop forever.
//
// This is the failure the read side already guards with wsPongWait: once the
// socket buffers fill, an unbounded WriteMessage blocks indefinitely. Because
// the ping ticker shares that loop, pings stop going out too, so neither end
// concludes the connection is dead and the caller waits forever.
func TestWriteLoopBoundsWritesOnAStalledPeer(t *testing.T) {
	// Shorten the bound so the test does not wait the production timeout.
	prev := wsWriteWait
	wsWriteWait = 250 * time.Millisecond
	defer func() { wsWriteWait = prev }()

	accepted := make(chan struct{})
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		conn, err := (&websocket.Upgrader{}).Upgrade(w, r, nil)
		if err != nil {
			return
		}
		// Accept the connection and then never read from it, so the client's
		// writes back up once the socket buffers fill.
		defer conn.Close()
		<-accepted
	}))
	defer server.Close()
	defer close(accepted)

	conn, resp, err := websocket.DefaultDialer.Dial("ws"+strings.TrimPrefix(server.URL, "http"), nil)
	if err != nil {
		t.Fatalf("dial: %v", err)
	}
	if resp != nil && resp.Body != nil {
		resp.Body.Close()
	}
	adapter := newWSAdapter(conn, false)
	defer adapter.Close()

	// Write until the buffers fill and the deadline has to do its job. A
	// stalled peer must surface an error rather than block.
	payload := make([]byte, 64<<10)
	done := make(chan error, 1)
	go func() {
		for {
			if err := adapter.WriteRaw(payload); err != nil {
				done <- err

				return
			}
		}
	}()

	select {
	case err := <-done:
		if err == nil {
			t.Fatal("want an error once the peer stops reading")
		}
	case <-time.After(30 * time.Second):
		t.Fatal("writes never returned: the write loop is wedged on a stalled peer")
	}
}
