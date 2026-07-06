package sprites

import (
	"context"
	"net"
	"net/http"
	"testing"
	"time"
)

func TestClientOptions(t *testing.T) {
	// Test default client
	client := New("test-token")
	if client.baseURL != "https://api.sprites.dev" {
		t.Errorf("default baseURL = %q, want %q", client.baseURL, "https://api.sprites.dev")
	}
	if client.token != "test-token" {
		t.Errorf("token = %q, want %q", client.token, "test-token")
	}

	// Test with custom base URL
	client = New("test-token", WithBaseURL("http://localhost:8080"))
	if client.baseURL != "http://localhost:8080" {
		t.Errorf("custom baseURL = %q, want %q", client.baseURL, "http://localhost:8080")
	}
}

// unwrapTransport extracts the underlying *http.Transport from a Client's
// httpClient, looking through the versionCapturingTransport wrapper.
func unwrapTransport(t *testing.T, c *Client) *http.Transport {
	t.Helper()

	vct, ok := c.httpClient.Transport.(*versionCapturingTransport)
	if !ok {
		t.Fatalf("expected c.httpClient.Transport to be *versionCapturingTransport, got %T", c.httpClient.Transport)
	}

	transport, ok := vct.wrapped.(*http.Transport)
	if !ok {
		t.Fatalf("expected wrapped transport to be *http.Transport, got %T", vct.wrapped)
	}

	return transport
}

func TestNew_DefaultTransportIsNotSharedGlobal(t *testing.T) {
	c := New("test-token")

	transport := unwrapTransport(t, c)

	if transport == http.DefaultTransport {
		t.Fatal("New() must not fall back to the shared http.DefaultTransport")
	}
	if transport.MaxIdleConnsPerHost <= 0 {
		t.Fatalf("expected a pooled transport (MaxIdleConnsPerHost > 0), got %d", transport.MaxIdleConnsPerHost)
	}
	if transport.DisableKeepAlives {
		t.Fatal("expected a pooled transport with keepalives enabled")
	}
}

func TestNew_WithHTTPClientNilDoesNotPanic(t *testing.T) {
	c := New("test-token", WithHTTPClient(nil))

	if c.httpClient == nil {
		t.Fatal("expected New() to restore a non-nil httpClient when WithHTTPClient(nil) is used")
	}

	transport := unwrapTransport(t, c)
	if transport == http.DefaultTransport {
		t.Fatal("New() must not fall back to the shared http.DefaultTransport")
	}
}

func TestWithNetDialContext_NilHTTPClientDoesNotPanic(t *testing.T) {
	fn := func(ctx context.Context, network, addr string) (net.Conn, error) {
		return nil, nil
	}

	c := New("test-token", WithHTTPClient(nil), WithNetDialContext(fn))

	transport := unwrapTransport(t, c)
	if transport.DialContext == nil {
		t.Fatal("expected DialContext to be set")
	}
}

func TestWithNetDialContext_PreservesExistingTransportSettings(t *testing.T) {
	const distinguishingTimeout = 42 * time.Second

	customTransport := &http.Transport{
		TLSHandshakeTimeout: distinguishingTimeout,
	}
	fn := func(ctx context.Context, network, addr string) (net.Conn, error) {
		return nil, nil
	}

	c := New("test-token",
		WithHTTPClient(&http.Client{Transport: customTransport}),
		WithNetDialContext(fn),
	)

	transport := unwrapTransport(t, c)

	if transport.TLSHandshakeTimeout != distinguishingTimeout {
		t.Fatalf("expected WithNetDialContext to preserve the existing transport's TLSHandshakeTimeout, got %v", transport.TLSHandshakeTimeout)
	}
	if transport.DialContext == nil {
		t.Fatal("expected DialContext to be set")
	}
	if transport == customTransport {
		t.Fatal("expected WithNetDialContext to clone the existing transport, not mutate it in place")
	}
}
