package proxy

import (
	"context"
	"fmt"
	"io"
	"log/slog"
	"net"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
	"time"
)

func TestParseProxyTarget(t *testing.T) {
	tests := []struct {
		name        string
		stateValue  string
		wantPort    int
		wantErr     bool
		errContains string
	}{
		{
			name:       "valid proxy format",
			stateValue: "proxy:mytoken:8080",
			wantPort:   8080,
			wantErr:    false,
		},
		{
			name:       "valid proxy with different port",
			stateValue: "proxy:abc123:3000",
			wantPort:   3000,
			wantErr:    false,
		},
		{
			name:        "invalid format - not proxy",
			stateValue:  "api:token",
			wantErr:     true,
			errContains: "invalid proxy format",
		},
		{
			name:        "invalid format - missing port",
			stateValue:  "proxy:token",
			wantErr:     true,
			errContains: "invalid proxy format",
		},
		{
			name:        "invalid port - not a number",
			stateValue:  "proxy:token:abc",
			wantErr:     true,
			errContains: "invalid port number",
		},
		{
			name:        "invalid port - out of range low",
			stateValue:  "proxy:token:0",
			wantErr:     true,
			errContains: "port number out of range",
		},
		{
			name:        "invalid port - out of range high",
			stateValue:  "proxy:token:70000",
			wantErr:     true,
			errContains: "port number out of range",
		},
		{
			name:        "empty state value",
			stateValue:  "",
			wantErr:     true,
			errContains: "invalid proxy format",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			port, err := ParseProxyTarget(tt.stateValue)

			if tt.wantErr {
				if err == nil {
					t.Errorf("ParseProxyTarget() expected error, got nil")
					return
				}
				if tt.errContains != "" && !strings.Contains(err.Error(), tt.errContains) {
					t.Errorf("ParseProxyTarget() error = %v, want error containing %v", err, tt.errContains)
				}
				return
			}

			if err != nil {
				t.Errorf("ParseProxyTarget() unexpected error = %v", err)
				return
			}

			if port != tt.wantPort {
				t.Errorf("ParseProxyTarget() port = %v, want %v", port, tt.wantPort)
			}
		})
	}
}

func TestProxyHandler(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	handler := NewHandler(logger)

	// Create a test backend server
	backend := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		// Echo back some request info
		w.Header().Set("X-Backend-Path", r.URL.Path)
		w.Header().Set("X-Backend-Method", r.Method)

		// Check for X-Forwarded headers
		if xff := r.Header.Get("X-Forwarded-For"); xff != "" {
			w.Header().Set("X-Forwarded-For-Echo", xff)
		}

		// Check that fly-replay-src was removed
		if r.Header.Get("fly-replay-src") != "" {
			w.Header().Set("X-Error", "fly-replay-src should be removed")
		}

		// Handle different paths
		switch r.URL.Path {
		case "/health":
			w.WriteHeader(http.StatusOK)
			w.Write([]byte("healthy"))
		case "/error":
			w.WriteHeader(http.StatusInternalServerError)
			w.Write([]byte("error"))
		case "/delay":
			time.Sleep(100 * time.Millisecond)
			w.Write([]byte("delayed"))
		default:
			w.Write([]byte("proxied response"))
		}
	}))
	defer backend.Close()

	// Extract port from backend URL
	backendPort := backend.Listener.Addr().(*net.TCPAddr).Port

	t.Run("successful proxy", func(t *testing.T) {
		req := httptest.NewRequest("GET", "/test/path", nil)
		ctx := context.WithValue(req.Context(), "stateValue", fmt.Sprintf("proxy:token:%d", backendPort))
		req = req.WithContext(ctx)

		rr := httptest.NewRecorder()
		handler.ServeHTTP(rr, req)

		if rr.Code != http.StatusOK {
			t.Errorf("handler returned wrong status code: got %v want %v", rr.Code, http.StatusOK)
		}

		body := rr.Body.String()
		if body != "proxied response" {
			t.Errorf("unexpected response body: %v", body)
		}

		// Check that backend received correct path
		if backendPath := rr.Header().Get("X-Backend-Path"); backendPath != "/test/path" {
			t.Errorf("backend received wrong path: %v", backendPath)
		}
	})

	t.Run("missing state value", func(t *testing.T) {
		req := httptest.NewRequest("GET", "/", nil)
		// Don't set state value in context

		rr := httptest.NewRecorder()
		handler.ServeHTTP(rr, req)

		if rr.Code != http.StatusInternalServerError {
			t.Errorf("handler returned wrong status code: got %v want %v", rr.Code, http.StatusInternalServerError)
		}

		if !strings.Contains(rr.Body.String(), "Missing proxy configuration") {
			t.Errorf("unexpected error message: %v", rr.Body.String())
		}
	})

	t.Run("connection refused", func(t *testing.T) {
		req := httptest.NewRequest("GET", "/", nil)
		// Use a port that's not listening
		ctx := context.WithValue(req.Context(), "stateValue", "proxy:token:59999")
		req = req.WithContext(ctx)

		rr := httptest.NewRecorder()
		handler.ServeHTTP(rr, req)

		if rr.Code != http.StatusServiceUnavailable {
			t.Errorf("handler returned wrong status code: got %v want %v", rr.Code, http.StatusServiceUnavailable)
		}

		if !strings.Contains(rr.Body.String(), "not available") {
			t.Errorf("unexpected error message: %v", rr.Body.String())
		}
	})

	t.Run("health check success", func(t *testing.T) {
		err := handler.HealthCheck(backendPort)
		if err != nil {
			t.Errorf("HealthCheck() unexpected error: %v", err)
		}
	})

	t.Run("health check failure", func(t *testing.T) {
		// Create a backend that returns 500 on health check
		unhealthyBackend := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			w.WriteHeader(http.StatusInternalServerError)
		}))
		defer unhealthyBackend.Close()

		unhealthyPort := unhealthyBackend.Listener.Addr().(*net.TCPAddr).Port

		err := handler.HealthCheck(unhealthyPort)
		if err == nil {
			t.Error("HealthCheck() expected error for unhealthy backend")
		}
		if !strings.Contains(err.Error(), "unhealthy status code") {
			t.Errorf("unexpected error: %v", err)
		}
	})
}
