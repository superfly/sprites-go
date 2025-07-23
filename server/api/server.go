package api

import (
	"context"
	"errors"
	"fmt"
	"log/slog"
	"net/http"
	"strings"
	"time"

	"github.com/sprite-env/server/api/handlers"
	"github.com/superfly/sprite-env/pkg/sync"
)

var (
	ErrNoAuth = errors.New("API token must be set - server cannot run without authentication")
)

// Server provides the HTTP API with authentication
type Server struct {
	server     *http.Server
	logger     *slog.Logger
	config     Config
	handlers   *handlers.Handlers
	system     handlers.SystemManager
	syncServer *sync.Server
}

// NewServer creates a new API server
func NewServer(config Config, system handlers.SystemManager, logger *slog.Logger) (*Server, error) {
	if config.APIToken == "" {
		return nil, ErrNoAuth
	}

	if config.MaxWaitTime == 0 {
		config.MaxWaitTime = 30 * time.Second
	}

	// Create handlers config
	handlersConfig := handlers.Config{
		MaxWaitTime:        config.MaxWaitTime,
		ExecWrapperCommand: config.ExecWrapperCommand,
	}

	// Create handlers
	h := handlers.NewHandlers(logger, system, handlersConfig)

	// Create sync server
	syncConfig := sync.ServerConfig{
		TargetBasePath: config.SyncTargetPath,
		MaxConnections: 10,
		Logger:         logger,
	}
	syncServer := sync.NewServer(syncConfig)

	s := &Server{
		logger:     logger,
		config:     config,
		handlers:   h,
		system:     system,
		syncServer: syncServer,
	}

	// Set up server
	mux := http.NewServeMux()
	s.setupEndpoints(mux)

	// Allow proxied requests with path prefix "/v1/sprites/:id/" to reuse the same handlers.
	// We wrap the mux with a small adapter that strips that prefix (and the dynamic ID)
	// before delegating to the real router.
	stripSpritePrefix := func(next http.Handler) http.Handler {
		return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			const prefix = "/v1/sprites/"
			if strings.HasPrefix(r.URL.Path, prefix) {
				// Remove the prefix, then strip the dynamic ID segment.
				trimmed := strings.TrimPrefix(r.URL.Path, prefix) // gives "<id>/exec" etc
				if idx := strings.IndexByte(trimmed, '/'); idx != -1 {
					newPath := trimmed[idx:] // includes leading slash
					// Clone request to avoid mutating original.
					r2 := r.Clone(r.Context())
					r2.URL.Path = newPath
					next.ServeHTTP(w, r2)
					return
				}
			}
			next.ServeHTTP(w, r)
		})
	}

	handler := stripSpritePrefix(mux)
	s.server = &http.Server{
		Addr: config.ListenAddr,
		Handler: http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			s.logger.Info("request", "url", r.URL.String())
			handler.ServeHTTP(w, r)
		}),
	}

	return s, nil
}

// setupEndpoints configures HTTP endpoints for the API
func (s *Server) setupEndpoints(mux *http.ServeMux) {
	// All other endpoints require authentication

	// Exec endpoint - waits for process to be running
	mux.HandleFunc("/exec", s.authMiddleware(s.waitForProcessMiddleware(s.handlers.HandleExec)))

	mux.HandleFunc("/sync", s.authMiddleware(s.waitForProcessMiddleware(s.syncServer.HandleWebSocket)))

	// Checkpoint endpoint - waits for JuiceFS to be ready
	mux.HandleFunc("/checkpoint", s.authMiddleware(s.waitForJuiceFSMiddleware(s.handlers.HandleCheckpoint)))

	// Transcripts toggle endpoints - waits for JuiceFS (and process) to be ready
	mux.HandleFunc("/transcripts/enable", s.authMiddleware(s.waitForJuiceFSMiddleware(s.handlers.HandleTranscriptsEnable)))
	mux.HandleFunc("/transcripts/disable", s.authMiddleware(s.waitForJuiceFSMiddleware(s.handlers.HandleTranscriptsDisable)))

	// Checkpoint management endpoints - wait for JuiceFS to be ready
	mux.HandleFunc("/checkpoints/", s.authMiddleware(s.waitForJuiceFSMiddleware(func(w http.ResponseWriter, r *http.Request) {
		// Route to appropriate handler based on path
		path := r.URL.Path
		parts := strings.Split(strings.Trim(path, "/"), "/")

		if len(parts) == 1 && parts[0] == "checkpoints" {
			// GET /checkpoints - list all checkpoints
			s.handlers.HandleListCheckpoints(w, r)
		} else if len(parts) == 2 {
			// GET /checkpoints/{id} - get specific checkpoint
			s.handlers.HandleGetCheckpoint(w, r)
		} else if len(parts) == 3 && parts[2] == "restore" {
			// POST /checkpoints/{id}/restore - restore from checkpoint
			s.handlers.HandleCheckpointRestore(w, r)
		} else {
			http.NotFound(w, r)
		}
	})))

	// Proxy endpoint - waits for process to be running
	mux.HandleFunc("/proxy", s.authMiddleware(s.waitForProcessMiddleware(s.handlers.HandleProxy)))

	// Debug endpoints - require auth but don't wait for process or JuiceFS
	mux.HandleFunc("/debug/create-zombie", s.authMiddleware(s.handlers.HandleDebugCreateZombie))
	mux.HandleFunc("/debug/check-process", s.authMiddleware(s.handlers.HandleDebugCheckProcess))

	// Admin endpoints - require admin auth
	mux.HandleFunc("/admin/reset-state", s.adminAuthMiddleware(s.handlers.HandleAdminResetState))
}

// Start starts the API server
func (s *Server) Start() error {
	s.logger.Info("Starting API server", "addr", s.server.Addr)
	return s.server.ListenAndServe()
}

// Stop stops the API server gracefully
func (s *Server) Stop(ctx context.Context) error {
	s.logger.Info("Stopping API server")
	return s.server.Shutdown(ctx)
}

// authMiddleware checks for authentication token
func (s *Server) authMiddleware(next http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		_, err := s.extractToken(r)
		if err != nil {
			http.Error(w, "Missing or invalid authentication", http.StatusUnauthorized)
			return
		}

		next(w, r)
	}
}

// adminAuthMiddleware checks for admin authentication token
// If AdminToken is set, it requires that specific token
// Otherwise falls back to regular auth
func (s *Server) adminAuthMiddleware(next http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		_, err := s.extractAdminToken(r)
		if err != nil {
			if s.config.AdminToken != "" {
				http.Error(w, "Admin authentication required", http.StatusForbidden)
			} else {
				http.Error(w, "Missing or invalid authentication", http.StatusUnauthorized)
			}
			return
		}

		next(w, r)
	}
}

// waitForProcessMiddleware waits for the process to be running before handling the request
func (s *Server) waitForProcessMiddleware(next http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		ctx, cancel := context.WithTimeout(r.Context(), s.config.MaxWaitTime)
		defer cancel()

		startTime := time.Now()

		// Use efficient waiting instead of polling
		err := s.system.WaitForProcessRunning(ctx)
		waitTime := time.Since(startTime)

		if err != nil {
			s.logger.Warn("Request timeout waiting for process to be running",
				"requestPath", r.URL.Path,
				"waitTime", waitTime,
				"error", err)
			http.Error(w, "Process not ready", http.StatusServiceUnavailable)
			return
		}

		// Log if we waited more than 5ms
		if waitTime > 5*time.Millisecond {
			s.logger.Info("Process became ready, processing request",
				"requestPath", r.URL.Path,
				"waitTime", waitTime)
		}

		next(w, r)
	}
}

// waitForJuiceFSMiddleware waits for JuiceFS to be ready before handling the request
func (s *Server) waitForJuiceFSMiddleware(next http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		ctx, cancel := context.WithTimeout(r.Context(), s.config.MaxWaitTime)
		defer cancel()

		startTime := time.Now()

		// Use efficient waiting
		err := s.system.WaitForJuiceFS(ctx)
		waitTime := time.Since(startTime)

		if err != nil {
			s.logger.Warn("Request timeout waiting for JuiceFS to be ready",
				"requestPath", r.URL.Path,
				"waitTime", waitTime,
				"error", err)
			http.Error(w, "Storage not ready", http.StatusServiceUnavailable)
			return
		}

		// Log if we waited more than 5ms
		if waitTime > 5*time.Millisecond {
			s.logger.Info("JuiceFS became ready, processing request",
				"requestPath", r.URL.Path,
				"waitTime", waitTime)
		}

		next(w, r)
	}
}

// extractToken extracts authentication token from either Authorization Bearer or fly-replay-src header
func (s *Server) extractToken(r *http.Request) (string, error) {
	var authToken, flyReplayToken string

	// First, check Authorization header
	authHeader := r.Header.Get("Authorization")
	if authHeader != "" {
		// Expected format: "Bearer <token>"
		parts := strings.SplitN(authHeader, " ", 2)
		if len(parts) == 2 && strings.ToLower(parts[0]) == "bearer" {
			authToken = strings.TrimSpace(parts[1])
			// Check if this token matches
			if authToken == s.config.APIToken {
				return authToken, nil
			}
			// Log that we found a token but it didn't match
			s.logger.Debug("Authorization header token found but doesn't match",
				"tokenProvided", maskToken(authToken),
				"tokenExpected", maskToken(s.config.APIToken))
		} else {
			s.logger.Debug("Authorization header present but not in Bearer format",
				"authHeader", authHeader,
				"expectedFormat", "Bearer <token>")
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
				// Check if this token matches
				if flyReplayToken == s.config.APIToken {
					return flyReplayToken, nil
				}
				// Log that we found a token but it didn't match
				s.logger.Debug("fly-replay-src state token found but doesn't match",
					"tokenProvided", maskToken(flyReplayToken),
					"tokenExpected", maskToken(s.config.APIToken))
				break
			}
		}
		if flyReplayToken == "" {
			// Debug log if header exists but no state found
			s.logger.Debug("fly-replay-src header present but no state parameter found",
				"flyReplayHeader", replayHeader)
		}
	}

	// Log error only when both methods fail, including any tokens that were found but not valid
	s.logger.Error("Token authentication failed - no matching token found",
		"authHeader", authHeader,
		"authTokenFound", maskToken(authToken),
		"flyReplayHeader", replayHeader,
		"flyReplayTokenFound", maskToken(flyReplayToken),
		"tokenExpected", maskToken(s.config.APIToken),
		"requestPath", r.URL.Path,
		"requestMethod", r.Method)

	return "", fmt.Errorf("no valid authentication token found")
}

// extractAdminToken extracts admin authentication token with the same fallback logic as extractToken
func (s *Server) extractAdminToken(r *http.Request) (string, error) {
	// If no admin token is configured, fall back to regular auth
	expectedToken := s.config.AdminToken
	if expectedToken == "" {
		expectedToken = s.config.APIToken
	}

	var authToken, flyReplayToken string

	// First, check Authorization header
	authHeader := r.Header.Get("Authorization")
	if authHeader != "" {
		// Expected format: "Bearer <token>"
		parts := strings.SplitN(authHeader, " ", 2)
		if len(parts) == 2 && strings.ToLower(parts[0]) == "bearer" {
			authToken = strings.TrimSpace(parts[1])
			// Check if this token matches
			if authToken == expectedToken {
				return authToken, nil
			}
			// Log that we found a token but it didn't match
			s.logger.Debug("Authorization header token found but doesn't match admin token",
				"tokenProvided", maskToken(authToken),
				"tokenExpected", maskToken(expectedToken))
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
				// Check if this token matches
				if flyReplayToken == expectedToken {
					return flyReplayToken, nil
				}
				// Log that we found a token but it didn't match
				s.logger.Debug("fly-replay-src state token found but doesn't match admin token",
					"tokenProvided", maskToken(flyReplayToken),
					"tokenExpected", maskToken(expectedToken))
				break
			}
		}
	}

	// Log error only when both methods fail
	s.logger.Error("Admin token authentication failed - no matching token found",
		"authHeader", authHeader,
		"authTokenFound", maskToken(authToken),
		"flyReplayHeader", replayHeader,
		"flyReplayTokenFound", maskToken(flyReplayToken),
		"tokenExpected", maskToken(expectedToken),
		"isAdminToken", s.config.AdminToken != "",
		"requestPath", r.URL.Path,
		"requestMethod", r.Method)

	return "", fmt.Errorf("no valid admin authentication token found")
}

// maskToken masks a token for safe logging, showing only the first 4 and last 4 characters
func maskToken(token string) string {
	if token == "" {
		return "(empty)"
	}
	if len(token) <= 10 {
		// Too short to mask effectively
		return strings.Repeat("*", len(token))
	}
	return token[:4] + "..." + token[len(token)-4:]
}
