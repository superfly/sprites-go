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
)

// Server provides the HTTP API with authentication
type Server struct {
	server   *http.Server
	logger   *slog.Logger
	config   Config
	handlers *handlers.Handlers
	system   handlers.SystemManager
}

// NewServer creates a new API server
func NewServer(config Config, system handlers.SystemManager, logger *slog.Logger) (*Server, error) {
	// Enforce authentication requirement
	if config.APIToken == "" {
		return nil, errors.New("API token must be set - server cannot run without authentication")
	}

	// Set default max wait time
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

	s := &Server{
		logger:   logger,
		config:   config,
		handlers: h,
		system:   system,
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

	s.server = &http.Server{
		Addr:    config.ListenAddr,
		Handler: stripSpritePrefix(mux),
	}

	return s, nil
}

// setupEndpoints configures HTTP endpoints for the API
func (s *Server) setupEndpoints(mux *http.ServeMux) {
	// Public endpoints (no authentication required)
	mux.HandleFunc("/v1/openapi.json", s.handlers.HandleOpenAPISpec)

	// All other endpoints require authentication

	// Exec endpoint - waits for process to be running
	mux.HandleFunc("/exec", s.authMiddleware(s.waitForProcessMiddleware(s.handlers.HandleExec)))

	// Checkpoint endpoint - waits for JuiceFS to be ready
	mux.HandleFunc("/checkpoint", s.authMiddleware(s.waitForJuiceFSMiddleware(s.handlers.HandleCheckpoint)))

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
		token, err := s.extractToken(r)
		if err != nil {
			http.Error(w, "Missing or invalid authentication", http.StatusUnauthorized)
			return
		}

		if token != s.config.APIToken {
			http.Error(w, "Invalid authentication token", http.StatusUnauthorized)
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
		token, err := s.extractToken(r)
		if err != nil {
			http.Error(w, "Missing or invalid authentication", http.StatusUnauthorized)
			return
		}

		// If admin token is configured, require it
		if s.config.AdminToken != "" {
			if token != s.config.AdminToken {
				http.Error(w, "Admin authentication required", http.StatusForbidden)
				return
			}
		} else {
			// Otherwise, accept regular API token
			if token != s.config.APIToken {
				http.Error(w, "Invalid authentication token", http.StatusUnauthorized)
				return
			}
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
	// First, check Authorization header
	authHeader := r.Header.Get("Authorization")
	if authHeader != "" {
		// Expected format: "Bearer <token>"
		parts := strings.SplitN(authHeader, " ", 2)
		if len(parts) == 2 && strings.ToLower(parts[0]) == "bearer" {
			return strings.TrimSpace(parts[1]), nil
		}
	}

	// Then check fly-replay-src header
	replayHeader := r.Header.Get("fly-replay-src")
	if replayHeader != "" {
		// Parse the fly-replay-src header for state=api:token format
		parts := strings.Split(replayHeader, ";")
		for _, part := range parts {
			kv := strings.SplitN(strings.TrimSpace(part), "=", 2)
			if len(kv) != 2 {
				continue
			}
			key := strings.TrimSpace(kv[0])
			value := strings.TrimSpace(kv[1])

			if key == "state" {
				// Parse state value expecting format: "api:token"
				stateParts := strings.SplitN(value, ":", 2)
				if len(stateParts) == 2 && stateParts[0] == "api" {
					return strings.TrimSpace(stateParts[1]), nil
				}
			}
		}
	}

	return "", fmt.Errorf("no valid authentication token found")
}
