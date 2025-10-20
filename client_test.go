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
	// Non-404 errors should not mark unsupported; supportsControl should remain default false until first use
	if sp.supportsControl {
		t.Fatalf("supportsControl should not be true by default")
	}
	// Call ensure again with a short context
	ctx, cancel := context.WithTimeout(context.Background(), 50*time.Millisecond)
	defer cancel()
	sp.ensureControlSupport(ctx)
	// Still not forced to false unless explicit 404
	if sp.supportsControl {
		t.Fatalf("supportsControl unexpectedly true")
	}
}
