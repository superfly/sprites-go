package api

import (
	"encoding/base64"
	"net/http/httptest"
	"strings"
	"testing"
)

func TestAuthManagerExtractToken(t *testing.T) {
	authManager := NewAuthManager("test-token", "")

	tests := []struct {
		name         string
		authHeader   string
		replayHeader string
		wantToken    string
		wantErr      bool
		errContains  string
	}{
		{
			name:       "valid Authorization Bearer token",
			authHeader: "Bearer test-token",
			wantToken:  "test-token",
			wantErr:    false,
		},
		{
			name:       "valid Authorization Bearer token with extra spaces",
			authHeader: "Bearer   test-token  ",
			wantToken:  "test-token",
			wantErr:    false,
		},
		{
			name:       "valid Basic auth with bearer username",
			authHeader: "Basic " + base64.StdEncoding.EncodeToString([]byte("bearer:test-token")),
			wantToken:  "test-token",
			wantErr:    false,
		},
		{
			name:       "Basic auth with wrong username",
			authHeader: "Basic " + base64.StdEncoding.EncodeToString([]byte("user:test-token")),
			wantErr:    true,
		},
		{
			name:       "Basic auth with invalid base64",
			authHeader: "Basic invalid-base64!",
			wantErr:    true,
		},
		{
			name:       "Basic auth with no colon",
			authHeader: "Basic " + base64.StdEncoding.EncodeToString([]byte("bearertest-token")),
			wantErr:    true,
		},
		{
			name:         "valid fly-replay-src header",
			replayHeader: "state=test-token",
			wantToken:    "test-token",
			wantErr:      false,
		},
		{
			name:         "fly-replay-src with other parameters",
			replayHeader: "region=ord;state=test-token;app=myapp",
			wantToken:    "test-token",
			wantErr:      false,
		},
		{
			name:         "fly-replay-src with spaces",
			replayHeader: "state= test-token ",
			wantToken:    "test-token",
			wantErr:      false,
		},
		{
			name:         "Authorization header takes precedence",
			authHeader:   "Bearer test-token",
			replayHeader: "state=invalid-token",
			wantToken:    "test-token",
			wantErr:      false,
		},
		{
			name:        "invalid Authorization format",
			authHeader:  "Digest dXNlcjpwYXNz",
			wantErr:     true,
			errContains: "no valid authentication token found",
		},
		{
			name:         "invalid fly-replay-src format - not api mode",
			replayHeader: "state=proxy:token:8080",
			wantErr:      true,
			errContains:  "no valid authentication token found",
		},
		{
			name:         "missing state in fly-replay-src",
			replayHeader: "region=ord;app=myapp",
			wantErr:      true,
			errContains:  "no valid authentication token found",
		},
		{
			name:        "no headers provided",
			wantErr:     true,
			errContains: "no valid authentication token found",
		},
		{
			name:        "Authorization with wrong format",
			authHeader:  "Bearer",
			wantErr:     true,
			errContains: "no valid authentication token found",
		},
		{
			name:       "case insensitive Bearer",
			authHeader: "bearer test-token",
			wantToken:  "test-token",
			wantErr:    false,
		},
		{
			name:       "BEARER uppercase",
			authHeader: "BEARER test-token",
			wantToken:  "test-token",
			wantErr:    false,
		},
		{
			name:       "wrong Bearer token",
			authHeader: "Bearer wrong-token",
			wantErr:    true,
		},
		{
			name:       "wrong Basic auth token",
			authHeader: "Basic " + base64.StdEncoding.EncodeToString([]byte("bearer:wrong-token")),
			wantErr:    true,
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

			token, err := authManager.ExtractToken(req)

			if tt.wantErr {
				if err == nil {
					t.Errorf("ExtractToken() expected error, got nil")
					return
				}
				if tt.errContains != "" && !strings.Contains(err.Error(), tt.errContains) {
					t.Errorf("ExtractToken() error = %v, want error containing %v", err, tt.errContains)
				}
				return
			}

			if err != nil {
				t.Errorf("ExtractToken() unexpected error = %v", err)
				return
			}

			if token != tt.wantToken {
				t.Errorf("ExtractToken() token = %v, want %v", token, tt.wantToken)
			}
		})
	}
}

func TestAuthManagerExtractAdminToken(t *testing.T) {
	tests := []struct {
		name         string
		apiToken     string
		adminToken   string
		authHeader   string
		replayHeader string
		wantToken    string
		wantErr      bool
	}{
		{
			name:       "admin token via Bearer",
			apiToken:   "api-token",
			adminToken: "admin-token",
			authHeader: "Bearer admin-token",
			wantToken:  "admin-token",
			wantErr:    false,
		},
		{
			name:       "admin token via Basic auth",
			apiToken:   "api-token",
			adminToken: "admin-token",
			authHeader: "Basic " + base64.StdEncoding.EncodeToString([]byte("bearer:admin-token")),
			wantToken:  "admin-token",
			wantErr:    false,
		},
		{
			name:         "admin token via fly-replay-src",
			apiToken:     "api-token",
			adminToken:   "admin-token",
			replayHeader: "state=admin-token",
			wantToken:    "admin-token",
			wantErr:      false,
		},
		{
			name:       "fallback to api token when no admin token set",
			apiToken:   "api-token",
			adminToken: "", // No admin token
			authHeader: "Bearer api-token",
			wantToken:  "api-token",
			wantErr:    false,
		},
		{
			name:       "api token not accepted when admin token is set",
			apiToken:   "api-token",
			adminToken: "admin-token",
			authHeader: "Bearer api-token",
			wantErr:    true,
		},
		{
			name:       "wrong admin token",
			apiToken:   "api-token",
			adminToken: "admin-token",
			authHeader: "Bearer wrong-token",
			wantErr:    true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			authManager := NewAuthManager(tt.apiToken, tt.adminToken)

			req := httptest.NewRequest("GET", "/admin/test", nil)
			if tt.authHeader != "" {
				req.Header.Set("Authorization", tt.authHeader)
			}
			if tt.replayHeader != "" {
				req.Header.Set("fly-replay-src", tt.replayHeader)
			}

			token, err := authManager.ExtractAdminToken(req)

			if tt.wantErr {
				if err == nil {
					t.Errorf("ExtractAdminToken() expected error, got nil")
				}
				return
			}

			if err != nil {
				t.Errorf("ExtractAdminToken() unexpected error = %v", err)
				return
			}

			if token != tt.wantToken {
				t.Errorf("ExtractAdminToken() token = %v, want %v", token, tt.wantToken)
			}
		})
	}
}

func TestAuthManagerHasAdminToken(t *testing.T) {
	tests := []struct {
		name       string
		adminToken string
		want       bool
	}{
		{
			name:       "has admin token",
			adminToken: "admin-token",
			want:       true,
		},
		{
			name:       "no admin token",
			adminToken: "",
			want:       false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			authManager := NewAuthManager("api-token", tt.adminToken)
			if got := authManager.HasAdminToken(); got != tt.want {
				t.Errorf("HasAdminToken() = %v, want %v", got, tt.want)
			}
		})
	}
}

func TestAuthManagerExtractTokenWithProxyCheck(t *testing.T) {
	authManager := NewAuthManager("test-token", "")

	tests := []struct {
		name         string
		authHeader   string
		replayHeader string
		wantToken    string
		wantIsProxy  bool
		wantErr      bool
		errContains  string
	}{
		{
			name:         "proxy token via fly-replay-src",
			replayHeader: "state=proxy::some-token-data",
			wantToken:    "some-token-data",
			wantIsProxy:  true,
			wantErr:      false,
		},
		{
			name:         "proxy token with additional parameters",
			replayHeader: "region=ord;state=proxy::another-token;app=myapp",
			wantToken:    "another-token",
			wantIsProxy:  true,
			wantErr:      false,
		},
		{
			name:         "regular token via fly-replay-src",
			replayHeader: "state=test-token",
			wantToken:    "test-token",
			wantIsProxy:  false,
			wantErr:      false,
		},
		{
			name:        "regular token via Bearer",
			authHeader:  "Bearer test-token",
			wantToken:   "test-token",
			wantIsProxy: false,
			wantErr:     false,
		},
		{
			name:         "proxy token takes precedence over Bearer",
			authHeader:   "Bearer test-token",
			replayHeader: "state=proxy::proxy-token",
			wantToken:    "proxy-token",
			wantIsProxy:  true,
			wantErr:      false,
		},
		{
			name:         "invalid proxy token (wrong api token after proxy::)",
			replayHeader: "state=proxy::wrong-token",
			wantToken:    "wrong-token",
			wantIsProxy:  true,
			wantErr:      false, // Proxy tokens are not validated against apiToken
		},
		{
			name:         "empty token after proxy::",
			replayHeader: "state=proxy::",
			wantToken:    "",
			wantIsProxy:  true,
			wantErr:      false,
		},
		{
			name:        "no authentication provided",
			wantErr:     true,
			errContains: "no valid authentication token found",
		},
		{
			name:         "invalid regular token",
			replayHeader: "state=wrong-token",
			wantErr:      true,
			errContains:  "no valid authentication token found",
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

			token, isProxy, err := authManager.ExtractTokenWithProxyCheck(req)

			if tt.wantErr {
				if err == nil {
					t.Errorf("ExtractTokenWithProxyCheck() expected error, got nil")
					return
				}
				if tt.errContains != "" && !strings.Contains(err.Error(), tt.errContains) {
					t.Errorf("ExtractTokenWithProxyCheck() error = %v, want error containing %v", err, tt.errContains)
				}
				return
			}

			if err != nil {
				t.Errorf("ExtractTokenWithProxyCheck() unexpected error = %v", err)
				return
			}

			if token != tt.wantToken {
				t.Errorf("ExtractTokenWithProxyCheck() token = %v, want %v", token, tt.wantToken)
			}

			if isProxy != tt.wantIsProxy {
				t.Errorf("ExtractTokenWithProxyCheck() isProxy = %v, want %v", isProxy, tt.wantIsProxy)
			}
		})
	}
}
