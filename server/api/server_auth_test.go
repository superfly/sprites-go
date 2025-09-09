package api

import (
	"context"
	"io"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"

	"github.com/superfly/sprite-env/pkg/tap"
)

func TestNewServerRequiresAuth(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	systemManager := newMockSystemManager()

	// Test that server creation fails without API token
	config := Config{
		ListenAddr: ":8080",
		APIToken:   "", // No token
	}

	_, err := NewServer(config, systemManager, ctx)
	if err == nil {
		t.Fatal("Expected error when creating server without API token, got nil")
	}

	if !strings.Contains(err.Error(), "API token must be set") {
		t.Errorf("Expected error about API token, got: %v", err)
	}

	// Test that server creation succeeds with API token
	config.APIToken = "test-token"
	server, err := NewServer(config, systemManager, ctx)
	if err != nil {
		t.Fatalf("Expected no error when creating server with API token, got: %v", err)
	}
	if server == nil {
		t.Fatal("Expected server instance, got nil")
	}
}

// TestExtractToken is now replaced by TestAuthManagerExtractToken in auth_test.go

func TestAuthMiddleware(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	systemManager := newMockSystemManager()

	tests := []struct {
		name           string
		apiToken       string
		authHeader     string
		replayHeader   string
		expectedStatus int
		expectedBody   string
	}{
		{
			name:           "valid Authorization Bearer token",
			apiToken:       "secret123",
			authHeader:     "Bearer secret123",
			expectedStatus: http.StatusOK,
		},
		{
			name:           "valid fly-replay-src token",
			apiToken:       "secret123",
			replayHeader:   "state=secret123",
			expectedStatus: http.StatusOK,
		},
		{
			name:           "invalid Bearer token",
			apiToken:       "secret123",
			authHeader:     "Bearer wrongtoken",
			expectedStatus: http.StatusUnauthorized,
			expectedBody:   "Missing or invalid authentication",
		},
		{
			name:           "invalid fly-replay-src token",
			apiToken:       "secret123",
			replayHeader:   "state=wrongtoken",
			expectedStatus: http.StatusUnauthorized,
			expectedBody:   "Missing or invalid authentication",
		},
		{
			name:           "missing authentication",
			apiToken:       "secret123",
			expectedStatus: http.StatusUnauthorized,
			expectedBody:   "Missing or invalid authentication",
		},
		{
			name:           "fly-replay-src with proxy mode ignored",
			apiToken:       "secret123",
			replayHeader:   "state=proxy:secret123:8080",
			expectedStatus: http.StatusUnauthorized,
			expectedBody:   "Missing or invalid authentication",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			config := Config{
				ListenAddr: ":8080",
				APIToken:   tt.apiToken,
			}
			server, _ := NewServer(config, systemManager, ctx)

			// Create a simple test handler
			testHandler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
				w.WriteHeader(http.StatusOK)
				w.Write([]byte("OK"))
			})

			// Wrap with auth middleware
			handler := server.authMiddleware(testHandler)

			// Create request
			req := httptest.NewRequest("GET", "/test", nil)
			if tt.authHeader != "" {
				req.Header.Set("Authorization", tt.authHeader)
			}
			if tt.replayHeader != "" {
				req.Header.Set("fly-replay-src", tt.replayHeader)
			}

			// Execute request
			rr := httptest.NewRecorder()
			handler.ServeHTTP(rr, req)

			// Check status
			if rr.Code != tt.expectedStatus {
				t.Errorf("handler returned wrong status code: got %v want %v", rr.Code, tt.expectedStatus)
			}

			// Check body if expected
			if tt.expectedBody != "" && !strings.Contains(rr.Body.String(), tt.expectedBody) {
				t.Errorf("handler returned unexpected body: got %v want containing %v", rr.Body.String(), tt.expectedBody)
			}
		})
	}
}
