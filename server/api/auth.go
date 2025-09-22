package api

import (
	"encoding/base64"
	"fmt"
	"net/http"
	"strings"
)

// AuthManager handles authentication for the API server
type AuthManager struct {
	apiToken   string
	adminToken string
}

// NewAuthManager creates a new authentication manager
func NewAuthManager(apiToken, adminToken string) *AuthManager {
	return &AuthManager{
		apiToken:   apiToken,
		adminToken: adminToken,
	}
}

// ExtractToken extracts authentication token from either Authorization (Bearer/Basic) or fly-replay-src header
func (a *AuthManager) ExtractToken(r *http.Request) (string, error) {
	var authToken, flyReplayToken string

	// First, check Authorization header
	authHeader := r.Header.Get("Authorization")
	if authHeader != "" {
		// Check for Bearer token format: "Bearer <token>" or Basic auth
		parts := strings.SplitN(authHeader, " ", 2)
		if len(parts) == 2 {
			authType := strings.ToLower(parts[0])

			if authType == "bearer" {
				// Handle Bearer token
				authToken = strings.TrimSpace(parts[1])
				if authToken == a.apiToken {
					return authToken, nil
				}
			} else if authType == "basic" {
				// Handle Basic auth with format "bearer:<token>"
				decoded, err := base64.StdEncoding.DecodeString(parts[1])
				if err == nil {
					// Expected format: "bearer:<token>"
					credentials := string(decoded)
					colonIdx := strings.IndexByte(credentials, ':')
					if colonIdx > 0 {
						username := credentials[:colonIdx]
						password := credentials[colonIdx+1:]

						if username == "bearer" {
							// Use the password as the token
							authToken = password
							if authToken == a.apiToken {
								return authToken, nil
							}
						}
					}
				}
			}
		}
	}

	// Then check fly-replay-src header
	replayHeader := r.Header.Get("fly-replay-src")
	if replayHeader != "" {
		// Parse the fly-replay-src header for state=token format
		parts := strings.Split(replayHeader, ";")
		for _, part := range parts {
			kv := strings.SplitN(strings.TrimSpace(part), "=", 2)
			if len(kv) != 2 {
				continue
			}
			key := strings.TrimSpace(kv[0])
			value := strings.TrimSpace(kv[1])

			if key == "state" {
				// Use the state value directly as the token
				flyReplayToken = strings.TrimSpace(value)
				if flyReplayToken == a.apiToken {
					return flyReplayToken, nil
				}
				break
			}
		}
	}

	return "", fmt.Errorf("no valid authentication token found")
}

// ExtractAdminToken extracts admin authentication token with the same logic as ExtractToken
// If no admin token is configured, falls back to regular auth
func (a *AuthManager) ExtractAdminToken(r *http.Request) (string, error) {
	// If no admin token is configured, fall back to regular auth
	expectedToken := a.adminToken
	if expectedToken == "" {
		expectedToken = a.apiToken
	}

	var authToken, flyReplayToken string

	// First, check Authorization header
	authHeader := r.Header.Get("Authorization")
	if authHeader != "" {
		// Check for Bearer token format: "Bearer <token>" or Basic auth
		parts := strings.SplitN(authHeader, " ", 2)
		if len(parts) == 2 {
			authType := strings.ToLower(parts[0])

			if authType == "bearer" {
				// Handle Bearer token
				authToken = strings.TrimSpace(parts[1])
				if authToken == expectedToken {
					return authToken, nil
				}
			} else if authType == "basic" {
				// Handle Basic auth with format "bearer:<token>"
				decoded, err := base64.StdEncoding.DecodeString(parts[1])
				if err == nil {
					// Expected format: "bearer:<token>"
					credentials := string(decoded)
					colonIdx := strings.IndexByte(credentials, ':')
					if colonIdx > 0 {
						username := credentials[:colonIdx]
						password := credentials[colonIdx+1:]

						if username == "bearer" {
							// Use the password as the token
							authToken = password
							if authToken == expectedToken {
								return authToken, nil
							}
						}
					}
				}
			}
		}
	}

	// Then check fly-replay-src header
	replayHeader := r.Header.Get("fly-replay-src")
	if replayHeader != "" {
		// Parse the fly-replay-src header for state=token format
		parts := strings.Split(replayHeader, ";")
		for _, part := range parts {
			kv := strings.SplitN(strings.TrimSpace(part), "=", 2)
			if len(kv) != 2 {
				continue
			}
			key := strings.TrimSpace(kv[0])
			value := strings.TrimSpace(kv[1])

			if key == "state" {
				// Use the state value directly as the token
				flyReplayToken = strings.TrimSpace(value)
				if flyReplayToken == expectedToken {
					return flyReplayToken, nil
				}
				break
			}
		}
	}

	return "", fmt.Errorf("no valid admin authentication token found")
}

// HasAdminToken returns true if a separate admin token is configured
func (a *AuthManager) HasAdminToken() bool {
	return a.adminToken != ""
}

// ExtractTokenWithProxyCheck extracts authentication token and checks if it's a proxy token
// Returns: token, isProxy, error
func (a *AuthManager) ExtractTokenWithProxyCheck(r *http.Request) (string, bool, error) {
	// Check fly-replay-src header first for proxy tokens
	replayHeader := r.Header.Get("fly-replay-src")
	if replayHeader != "" {
		// Parse the fly-replay-src header for state=token format
		parts := strings.Split(replayHeader, ";")
		for _, part := range parts {
			kv := strings.SplitN(strings.TrimSpace(part), "=", 2)
			if len(kv) != 2 {
				continue
			}
			key := strings.TrimSpace(kv[0])
			value := strings.TrimSpace(kv[1])

			if key == "state" {
				// Check if it's a proxy token
				stateValue := strings.TrimSpace(value)
				if strings.HasPrefix(stateValue, "proxy::") {
					// Extract the actual token after proxy::
					actualToken := strings.TrimPrefix(stateValue, "proxy::")
					// For proxy tokens, we don't validate against apiToken
					// The proxy destination will handle authentication
					return actualToken, true, nil
				}
				break
			}
		}
	}

	// If not a proxy token, use regular authentication
	token, err := a.ExtractToken(r)
	return token, false, err
}
