package sprites

import (
	"context"
	"net/http"
	"net/http/httptest"
	"os"
	"strings"
	"testing"
	"time"

	"github.com/gorilla/websocket"
)

// endlessReader returns data forever so the write loop stays busy.
type endlessReader struct{}

func (endlessReader) Read(p []byte) (int, error) {
	for i := range p {
		p[i] = 'x'
	}

	return len(p), nil
}

func newExitingServer(t *testing.T, exitFrame func(*websocket.Conn) error) *httptest.Server {
	t.Helper()

	return httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		conn, err := (&websocket.Upgrader{}).Upgrade(w, r, nil)
		if err != nil {
			return
		}
		defer conn.Close()
		go func() {
			for {
				if _, _, err := conn.ReadMessage(); err != nil {
					return
				}
			}
		}()
		_ = exitFrame(conn)
		time.Sleep(50 * time.Millisecond)
	}))
}

func wsURL(server *httptest.Server) string {
	return "ws" + strings.TrimPrefix(server.URL, "http")
}

// Close used to call SetWriteDeadline on the connection while the adapter's
// write loop could still be inside WriteMessage. Run with -race.
func TestCloseDoesNotRaceWriteLoop(t *testing.T) {
	server := newExitingServer(t, func(conn *websocket.Conn) error {
		time.Sleep(5 * time.Millisecond)
		return conn.WriteMessage(websocket.BinaryMessage, []byte{byte(StreamExit), 0})
	})
	defer server.Close()

	for i := 0; i < 20; i++ {
		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		req, err := http.NewRequestWithContext(ctx, http.MethodGet, wsURL(server), nil)
		if err != nil {
			cancel()
			t.Fatalf("NewRequestWithContext() error = %v", err)
		}
		wsCmd := newWSCmdContext(ctx, req, "cat")
		wsCmd.Stdin = endlessReader{}
		if err := wsCmd.Start(); err != nil {
			cancel()
			t.Fatalf("Start() error = %v", err)
		}
		_ = wsCmd.Wait()
		cancel()
	}
}

// The TTY resize goroutine used to read the os.Stdin global 10ms after
// start, so a caller that swapped os.Stdin and restored it once the command
// finished raced with it. Run with -race.
func TestTTYResizeDoesNotReadStdinAfterCommandReturns(t *testing.T) {
	server := newExitingServer(t, func(conn *websocket.Conn) error {
		// Exit after the resize goroutine's 10ms delay, so it gets past the
		// select and reads stdin while the command is still running.
		time.Sleep(50 * time.Millisecond)
		return conn.WriteMessage(websocket.TextMessage, []byte(`{"type":"exit","exit_code":0}`))
	})
	defer server.Close()

	stdinReader, stdinWriter, err := os.Pipe()
	if err != nil {
		t.Fatalf("os.Pipe() error = %v", err)
	}
	defer stdinReader.Close()
	defer stdinWriter.Close()

	original := os.Stdin
	os.Stdin = stdinReader
	t.Cleanup(func() { os.Stdin = original })

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, wsURL(server), nil)
	if err != nil {
		t.Fatalf("NewRequestWithContext() error = %v", err)
	}
	wsCmd := newWSCmdContext(ctx, req, "sh")
	wsCmd.Tty = true
	if err := wsCmd.Start(); err != nil {
		t.Fatalf("Start() error = %v", err)
	}
	_ = wsCmd.Wait()

	os.Stdin = original
	// Give a detached resize goroutine time to run if one is still pending.
	time.Sleep(30 * time.Millisecond)
}

// proxyConn.Close used to call SetWriteDeadline on the connection outside
// writeMu, racing with a concurrent Write inside WriteMessage. net.Conn
// allows Close to be called while Write is in progress. Run with -race.
func TestProxyConnCloseDoesNotRaceWrite(t *testing.T) {
	server := newExitingServer(t, func(*websocket.Conn) error {
		return nil
	})
	defer server.Close()

	for i := 0; i < 20; i++ {
		ws, resp, err := websocket.DefaultDialer.Dial(wsURL(server), nil)
		if err != nil {
			t.Fatalf("Dial() error = %v", err)
		}
		resp.Body.Close()
		conn := &proxyConn{conn: ws}

		done := make(chan struct{})
		go func() {
			defer close(done)
			buf := make([]byte, 1024)
			for {
				if _, err := conn.Write(buf); err != nil {
					return
				}
			}
		}()
		time.Sleep(2 * time.Millisecond)
		if err := conn.Close(); err != nil {
			t.Fatalf("Close() error = %v", err)
		}
		<-done
	}
}
