package sprites

import (
	"context"
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

func TestControlFallbackOn404Only(t *testing.T) {
	client := New("test-token", WithBaseURL("http://localhost:65535")) // unreachable host to trigger non-404
	client.controlInitTimeout = 50 * time.Millisecond
	sp := client.Sprite("foo")
	// Non-404 errors should default transport to endpoint without failing hard
	ctx, cancel := context.WithTimeout(context.Background(), 50*time.Millisecond)
	defer cancel()
	_ = sp.probeControlSupport(ctx)
	if sp.transport != "endpoint" {
		t.Fatalf("expected transport endpoint, got %s", sp.transport)
	}
}
