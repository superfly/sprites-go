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

func TestParseReplayState(t *testing.T) {
	tests := []struct {
		name           string
		headerValue    string
		wantToken      string
		wantMode       string
		wantStateValue string
		wantErr        bool
		errContains    string
	}{
		{
			name:           "valid api mode",
			headerValue:    "state=api:mysecrettoken",
			wantToken:      "mysecrettoken",
			wantMode:       "api",
			wantStateValue: "api:mysecrettoken",
			wantErr:        false,
		},
		{
			name:           "valid proxy mode",
			headerValue:    "state=proxy:token123:8080",
			wantToken:      "token123:8080",
			wantMode:       "proxy",
			wantStateValue: "proxy:token123:8080",
			wantErr:        false,
		},
		{
			name:           "with other parameters",
			headerValue:    "region=ord;state=api:token;app=myapp",
			wantToken:      "token",
			wantMode:       "api",
			wantStateValue: "api:token",
			wantErr:        false,
		},
		{
			name:           "spaces around values",
			headerValue:    "state= api: token123 ",
			wantToken:      "token123",
			wantMode:       "api",
			wantStateValue: "api:token123",
			wantErr:        false,
		},
		{
			name:        "missing state key",
			headerValue: "region=ord;app=myapp",
			wantErr:     true,
			errContains: "missing state",
		},
		{
			name:        "invalid state format - no colon",
			headerValue: "state=apitoken",
			wantErr:     true,
			errContains: "invalid state format",
		},
		{
			name:        "missing token",
			headerValue: "state=api:",
			wantErr:     true,
			errContains: "missing token",
		},
		{
			name:        "missing mode",
			headerValue: "state=:token",
			wantErr:     true,
			errContains: "missing mode",
		},
		{
			name:        "empty header",
			headerValue: "",
			wantErr:     true,
			errContains: "missing state",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			token, mode, stateValue, err := parseReplayState(tt.headerValue)

			if tt.wantErr {
				if err == nil {
					t.Errorf("parseReplayState() expected error, got nil")
					return
				}
				if tt.errContains != "" && !strings.Contains(err.Error(), tt.errContains) {
					t.Errorf("parseReplayState() error = %v, want error containing %v", err, tt.errContains)
				}
				return
			}

			if err != nil {
				t.Errorf("parseReplayState() unexpected error = %v", err)
				return
			}

			if token != tt.wantToken {
				t.Errorf("parseReplayState() token = %v, want %v", token, tt.wantToken)
			}
			if mode != tt.wantMode {
				t.Errorf("parseReplayState() mode = %v, want %v", mode, tt.wantMode)
			}
			if stateValue != tt.wantStateValue {
				t.Errorf("parseReplayState() stateValue = %v, want %v", stateValue, tt.wantStateValue)
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
		replayHeader   string
		requiredMode   string
		expectedStatus int
		expectedBody   string
	}{
		{
			name:           "valid api mode with token",
			apiToken:       "secret123",
			replayHeader:   "state=api:secret123",
			requiredMode:   "api",
			expectedStatus: http.StatusOK,
		},
		{
			name:           "invalid token",
			apiToken:       "secret123",
			replayHeader:   "state=api:wrongtoken",
			requiredMode:   "api",
			expectedStatus: http.StatusUnauthorized,
			expectedBody:   "Invalid authentication token",
		},
		{
			name:           "missing header",
			apiToken:       "secret123",
			replayHeader:   "",
			requiredMode:   "api",
			expectedStatus: http.StatusUnauthorized,
			expectedBody:   "Missing fly-replay-src header",
		},
		{
			name:           "invalid header format",
			apiToken:       "secret123",
			replayHeader:   "state=invalid",
			requiredMode:   "api",
			expectedStatus: http.StatusBadRequest,
			expectedBody:   "Invalid replay state",
		},
		{
			name:           "proxy mode accessing api endpoint",
			apiToken:       "secret123",
			replayHeader:   "state=proxy:secret123:8080",
			requiredMode:   "api",
			expectedStatus: http.StatusNotFound,
			expectedBody:   "not available in proxy mode",
		},
		{
			name:           "api mode accessing proxy endpoint",
			apiToken:       "secret123",
			replayHeader:   "state=api:secret123",
			requiredMode:   "proxy",
			expectedStatus: http.StatusNotFound,
			expectedBody:   "Not found",
		},
		{
			name:           "valid proxy mode",
			apiToken:       "secret123",
			replayHeader:   "state=proxy:secret123:8080",
			requiredMode:   "proxy",
			expectedStatus: http.StatusOK,
		},
		{
			name:           "no auth required",
			apiToken:       "",
			replayHeader:   "state=api:anytoken",
			requiredMode:   "api",
			expectedStatus: http.StatusOK,
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
			handler := server.authMiddleware(testHandler, tt.requiredMode)

			// Create request
			req := httptest.NewRequest("GET", "/test", nil)
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
