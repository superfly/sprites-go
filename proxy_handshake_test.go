package sprites

import (
	"context"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
)

// TestDialProxyWebSocketReportsHandshakeStatus checks that a refused proxy
// handshake names the HTTP status.
//
// gorilla returns the same opaque "websocket: bad handshake" whatever the
// server said, so without the status a 401, a 404 and a 502 are
// indistinguishable — and they point at completely different culprits: the
// caller's token, the requested sprite, or the control plane.
func TestDialProxyWebSocketReportsHandshakeStatus(t *testing.T) {
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		http.Error(w, "upstream unavailable", http.StatusBadGateway)
	}))
	defer server.Close()

	client := NewClient(server.URL, "test-token")
	_, err := client.dialProxyWebSocket(context.Background(), "test-sprite")
	if err == nil {
		t.Fatal("want an error when the handshake is refused")
	}
	if !strings.Contains(err.Error(), "HTTP 502") {
		t.Errorf("error does not name the status: %v", err)
	}
	if !strings.Contains(err.Error(), "upstream unavailable") {
		t.Errorf("error does not carry the server's explanation: %v", err)
	}
}

// TestDialProxyWebSocketRedactsCredentials checks that the added diagnostics
// cannot leak the bearer token, which is sent on every proxy dial.
func TestDialProxyWebSocketRedactsCredentials(t *testing.T) {
	const token = "super-secret-token"
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		// A server that echoes the request's credentials back in its body.
		http.Error(w, "rejected: "+r.Header.Get("Authorization"), http.StatusUnauthorized)
	}))
	defer server.Close()

	client := NewClient(server.URL, token)
	_, err := client.dialProxyWebSocket(context.Background(), "test-sprite")
	if err == nil {
		t.Fatal("want an error when the handshake is refused")
	}
	if strings.Contains(err.Error(), token) {
		t.Errorf("leaked the token: %v", err)
	}
	if !strings.Contains(err.Error(), "HTTP 401") {
		t.Errorf("error does not name the status: %v", err)
	}
}
