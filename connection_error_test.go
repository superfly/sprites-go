package sprites

import (
	"context"
	"errors"
	"fmt"
	"io"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"

	"github.com/gorilla/websocket"
)

func TestCommandConnectionDiagnostics(t *testing.T) {
	for _, code := range []int{200, 302, 401, 429, 503} {
		for _, body := range []string{"", `{"message":"service temporarily unavailable"}`, "upstream rejected handshake"} {
			t.Run(fmt.Sprintf("%d/%s", code, body), func(t *testing.T) {
				srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
					w.Header().Set("Fly-Request-Id", "fly-123")
					w.Header().Set("X-Request-Id", "req-456")
					w.Header().Set("X-Correlation-Id", "corr-789")
					w.WriteHeader(code)
					io.WriteString(w, body)
				}))
				defer srv.Close()
				client := New("secret-token", WithBaseURL(srv.URL), WithDisableControl())
				for _, control := range []bool{false, true} {
					var err error
					if control {
						_, err = client.getOrCreatePool("test").dial(context.Background())
					} else {
						err = client.Sprite("test").Command("true").Start()
					}
					if err == nil {
						t.Fatal("expected rejection")
					}
					for _, want := range []string{fmt.Sprintf("HTTP %d", code), "fly-request-id: fly-123", "x-request-id: req-456", "x-correlation-id: corr-789", "websocket: bad handshake"} {
						if !strings.Contains(err.Error(), want) {
							t.Errorf("%q missing %q", err, want)
						}
					}
					if !errors.Is(err, websocket.ErrBadHandshake) {
						t.Errorf("lost handshake cause: %v", err)
					}
					if code >= 400 {
						var apiErr *APIError
						if !errors.As(err, &apiErr) || apiErr.StatusCode != code || apiErr.RequestID != "fly-123" {
							t.Errorf("lost API metadata: %v", err)
						}
					}
				}
			})
		}
	}
}

func TestConnectionDiagnosticsRedactionAndBounds(t *testing.T) {
	header := http.Header{"Authorization": {"Bearer actual-secret"}, "Cookie": {"session=cookie-secret"}}
	body := "actual-secret cookie-secret\nAuthorization: Bearer another-secret\nhttps://user:password@example.com/?token=query-secret\n\x1b[31m" + strings.Repeat("x", 10000)
	resp := &http.Response{StatusCode: 503, Header: http.Header{"Fly-Request-Id": {"fly-123"}}, Body: io.NopCloser(strings.NewReader(body))}
	err := commandConnectionError("failed to connect", websocket.ErrBadHandshake, resp, header)
	for _, secret := range []string{"actual-secret", "cookie-secret", "another-secret", "password", "query-secret", "\x1b", "\n"} {
		if strings.Contains(err.Error(), secret) {
			t.Errorf("leaked %q: %v", secret, err)
		}
	}
	if len(err.Error()) > 700 {
		t.Fatalf("unbounded error: %d", len(err.Error()))
	}
	// CLI prefixes plus a 300-byte harness limit still retain correlation.
	evidence := ("Error: failed to start sprite command: " + err.Error())[:300]
	if !strings.Contains(evidence, "HTTP 503); fly-request-id: fly-123") {
		t.Fatalf("lost evidence: %s", evidence)
	}
}

func TestConnectionDiagnosticsTransportCause(t *testing.T) {
	err := commandConnectionError("failed to connect", context.DeadlineExceeded, nil, nil)
	if !errors.Is(err, context.DeadlineExceeded) {
		t.Fatal("lost cancellation")
	}
	if strings.Contains(err.Error(), "HTTP") {
		t.Fatalf("invented HTTP response: %v", err)
	}
}

type interruptedConnectionBody struct {
	closed bool
	read   bool
}

func (b *interruptedConnectionBody) Read(p []byte) (int, error) {
	if b.read {
		return 0, io.ErrUnexpectedEOF
	}
	b.read = true
	return copy(p, "upstream unavailable"), io.ErrUnexpectedEOF
}
func (b *interruptedConnectionBody) Close() error { b.closed = true; return nil }

func TestConnectionDiagnosticsPartialBody(t *testing.T) {
	body := &interruptedConnectionBody{}
	resp := &http.Response{StatusCode: 502, Header: http.Header{"Fly-Request-Id": {"fly-123"}}, Body: body}
	err := commandConnectionError("failed to connect", websocket.ErrBadHandshake, resp, nil)
	if !body.closed {
		t.Fatal("response body not closed")
	}
	for _, want := range []string{"HTTP 502", "fly-123", "upstream unavailable"} {
		if !strings.Contains(err.Error(), want) {
			t.Errorf("lost %q: %v", want, err)
		}
	}
}
