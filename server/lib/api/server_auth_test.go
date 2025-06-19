package api

import (
	"io"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"os"
	"strings"
	"testing"

	"sprite-env/lib"
)

func TestExtractToken(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	mockState := &mockSystemState{}
	
	// Create a test config
	config := &lib.ApplicationConfig{
		Exec: lib.ExecConfig{
			WrapperCommand:    []string{},
			TTYWrapperCommand: []string{},
		},
	}
	
	server := NewServer(":8080", mockState, logger, config)
	
	tests := []struct {
		name            string
		authHeader      string
		replayHeader    string
		wantToken       string
		wantErr         bool
		errContains     string
	}{
		{
			name:       "valid Authorization Bearer token",
			authHeader: "Bearer mysecrettoken",
			wantToken:  "mysecrettoken",
			wantErr:    false,
		},
		{
			name:       "valid Authorization Bearer token with extra spaces",
			authHeader: "Bearer   mysecrettoken  ",
			wantToken:  "mysecrettoken",
			wantErr:    false,
		},
		{
			name:       "valid fly-replay-src header",
			replayHeader: "state=api:token123",
			wantToken:   "token123",
			wantErr:     false,
		},
		{
			name:       "fly-replay-src with other parameters",
			replayHeader: "region=ord;state=api:mytoken;app=myapp",
			wantToken:   "mytoken",
			wantErr:     false,
		},
		{
			name:       "fly-replay-src with spaces",
			replayHeader: "state= api: token456 ",
			wantToken:   "token456",
			wantErr:     false,
		},
		{
			name:       "Authorization header takes precedence",
			authHeader: "Bearer bearertoken",
			replayHeader: "state=api:replaytoken",
			wantToken:   "bearertoken",
			wantErr:     false,
		},
		{
			name:       "invalid Authorization format",
			authHeader: "Basic dXNlcjpwYXNz",
			wantErr:    true,
			errContains: "no valid authentication token found",
		},
		{
			name:       "invalid fly-replay-src format - not api mode",
			replayHeader: "state=proxy:token:8080",
			wantErr:     true,
			errContains: "no valid authentication token found",
		},
		{
			name:       "missing state in fly-replay-src",
			replayHeader: "region=ord;app=myapp",
			wantErr:     true,
			errContains: "no valid authentication token found",
		},
		{
			name:       "no headers provided",
			wantErr:    true,
			errContains: "no valid authentication token found",
		},
		{
			name:       "Authorization with wrong format",
			authHeader: "Bearer",
			wantErr:    true,
			errContains: "no valid authentication token found",
		},
		{
			name:       "case insensitive Bearer",
			authHeader: "bearer mysecrettoken",
			wantToken:  "mysecrettoken",
			wantErr:    false,
		},
		{
			name:       "BEARER uppercase",
			authHeader: "BEARER mysecrettoken",
			wantToken:  "mysecrettoken",
			wantErr:    false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			req := httptest.NewRequest("GET", "/test", nil)
			if tt.authHeader != "" {
				req.Header.Set("Authorization", tt.authHeader)
			}
			if tt.replayHeader != "" {
				req.Header.Set("fly-replay-src", tt.replayHeader)
			}

			token, err := server.extractToken(req)

			if tt.wantErr {
				if err == nil {
					t.Errorf("extractToken() expected error, got nil")
					return
				}
				if tt.errContains != "" && !strings.Contains(err.Error(), tt.errContains) {
					t.Errorf("extractToken() error = %v, want error containing %v", err, tt.errContains)
				}
				return
			}

			if err != nil {
				t.Errorf("extractToken() unexpected error = %v", err)
				return
			}

			if token != tt.wantToken {
				t.Errorf("extractToken() token = %v, want %v", token, tt.wantToken)
			}
		})
	}
}

func TestAuthMiddleware(t *testing.T) {
	// Save and restore env var
	oldToken := os.Getenv("SPRITE_HTTP_API_TOKEN")
	defer os.Setenv("SPRITE_HTTP_API_TOKEN", oldToken)

	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	mockState := &mockSystemState{}

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
			replayHeader:   "state=api:secret123",
			expectedStatus: http.StatusOK,
		},
		{
			name:           "invalid Bearer token",
			apiToken:       "secret123",
			authHeader:     "Bearer wrongtoken",
			expectedStatus: http.StatusUnauthorized,
			expectedBody:   "Invalid authentication token",
		},
		{
			name:           "invalid fly-replay-src token",
			apiToken:       "secret123",
			replayHeader:   "state=api:wrongtoken",
			expectedStatus: http.StatusUnauthorized,
			expectedBody:   "Invalid authentication token",
		},
		{
			name:           "missing authentication",
			apiToken:       "secret123",
			expectedStatus: http.StatusUnauthorized,
			expectedBody:   "Missing or invalid authentication",
		},
		{
			name:           "no auth required when token not configured",
			apiToken:       "",
			expectedStatus: http.StatusOK,
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
			os.Setenv("SPRITE_HTTP_API_TOKEN", tt.apiToken)
			// Create a test config
			config := &lib.ApplicationConfig{
				Exec: lib.ExecConfig{
					WrapperCommand:    []string{},
					TTYWrapperCommand: []string{},
				},
			}
			server := NewServer(":8080", mockState, logger, config)

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
