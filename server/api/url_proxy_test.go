package api

import (
	"fmt"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
)

func TestExtractProxyToken(t *testing.T) {
	tests := []struct {
		name            string
		token           string
		wantActualToken string
		wantIsProxy     bool
	}{
		{
			name:            "proxy token",
			token:           "proxy::some-token-data",
			wantActualToken: "some-token-data",
			wantIsProxy:     true,
		},
		{
			name:            "regular token",
			token:           "regular-token",
			wantActualToken: "regular-token",
			wantIsProxy:     false,
		},
		{
			name:            "empty proxy token",
			token:           "proxy::",
			wantActualToken: "",
			wantIsProxy:     true,
		},
		{
			name:            "token with proxy:: in middle",
			token:           "someproxy::token",
			wantActualToken: "someproxy::token",
			wantIsProxy:     false,
		},
		{
			name:            "empty token",
			token:           "",
			wantActualToken: "",
			wantIsProxy:     false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			actualToken, isProxy := ExtractProxyToken(tt.token)
			if actualToken != tt.wantActualToken {
				t.Errorf("ExtractProxyToken() actualToken = %v, want %v", actualToken, tt.wantActualToken)
			}
			if isProxy != tt.wantIsProxy {
				t.Errorf("ExtractProxyToken() isProxy = %v, want %v", isProxy, tt.wantIsProxy)
			}
		})
	}
}

func TestProxyHandler(t *testing.T) {
	// Create a test backend server
	backend := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		// Echo back some request details
		w.Header().Set("X-Backend-Response", "true")

		// Check that fly-replay-src header is removed
		if r.Header.Get("fly-replay-src") != "" {
			t.Error("fly-replay-src header should be removed before proxying")
		}

		fmt.Fprintf(w, "Backend response: %s %s", r.Method, r.URL.Path)
	}))
	defer backend.Close()

	// Parse backend URL to get host and port
	backendURL := strings.TrimPrefix(backend.URL, "http://")
	parts := strings.Split(backendURL, ":")
	if len(parts) != 2 {
		t.Fatalf("Invalid backend URL format: %s", backend.URL)
	}

	port := 0
	fmt.Sscanf(parts[1], "%d", &port)

	// Create proxy handler
	logger := slog.Default()
	handler := NewProxyHandler(logger, parts[0], port)

	// Test cases
	tests := []struct {
		name       string
		method     string
		path       string
		headers    map[string]string
		wantStatus int
	}{
		{
			name:       "GET request",
			method:     "GET",
			path:       "/test",
			wantStatus: http.StatusOK,
		},
		{
			name:       "POST request",
			method:     "POST",
			path:       "/api/endpoint",
			wantStatus: http.StatusOK,
		},
		{
			name:   "Request with fly-replay-src header",
			method: "GET",
			path:   "/test",
			headers: map[string]string{
				"fly-replay-src": "state=proxy::token",
			},
			wantStatus: http.StatusOK,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			req := httptest.NewRequest(tt.method, tt.path, nil)
			for k, v := range tt.headers {
				req.Header.Set(k, v)
			}

			rec := httptest.NewRecorder()
			handler.ServeHTTP(rec, req)

			if rec.Code != tt.wantStatus {
				t.Errorf("ProxyHandler.ServeHTTP() status = %v, want %v", rec.Code, tt.wantStatus)
			}

			// Check that we got a response from the backend
			if !strings.Contains(rec.Body.String(), "Backend response") {
				t.Errorf("Expected backend response, got: %s", rec.Body.String())
			}

			// Check that backend set its header
			if rec.Header().Get("X-Backend-Response") != "true" {
				t.Error("Expected X-Backend-Response header from backend")
			}
		})
	}
}

func TestProxyHandlerErrorHandling(t *testing.T) {
	// Create proxy handler pointing to non-existent backend
	logger := slog.Default()
	handler := NewProxyHandler(logger, "localhost", 99999) // Invalid port

	req := httptest.NewRequest("GET", "/test", nil)
	rec := httptest.NewRecorder()

	handler.ServeHTTP(rec, req)

	// Should return bad gateway when backend is unreachable
	if rec.Code != http.StatusBadGateway {
		t.Errorf("Expected status %d for unreachable backend, got %d", http.StatusBadGateway, rec.Code)
	}

	if !strings.Contains(rec.Body.String(), "Proxy error") {
		t.Errorf("Expected 'Proxy error' message, got: %s", rec.Body.String())
	}
}
