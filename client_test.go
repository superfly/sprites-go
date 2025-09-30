package sprites

import (
	"testing"
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
