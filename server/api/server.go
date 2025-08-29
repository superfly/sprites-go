package api

import (
	"context"
	"errors"
	"log/slog"
	"net/http"
	"strings"
	"time"

	"github.com/superfly/sprite-env/server/api/handlers"
	"github.com/superfly/sprite-env/pkg/sync"
)

var (
	ErrNoAuth = errors.New("API token must be set - server cannot run without authentication")
)

// Server provides the HTTP API with authentication
type Server struct {
	server      *http.Server
	logger      *slog.Logger
	config      Config
	handlers    *handlers.Handlers
	system      handlers.SystemManager
	syncServer  *sync.Server
	authManager *AuthManager
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
		ProxyLocalhostIPv4: config.ProxyLocalhostIPv4,
		ProxyLocalhostIPv6: config.ProxyLocalhostIPv6,
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

	// Create auth manager
	authManager := NewAuthManager(config.APIToken, config.AdminToken)

	s := &Server{
		logger:      logger,
		config:      config,
		handlers:    h,
		system:      system,
		syncServer:  syncServer,
		authManager: authManager,
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

	// Checkpoint management endpoints - wait for JuiceFS to be ready
	// This pattern matches /checkpoints and any subpaths like /checkpoints/{id} or /checkpoints/{id}/restore
	checkpointsHandler := s.authMiddleware(s.waitForJuiceFSMiddleware(func(w http.ResponseWriter, r *http.Request) {
		// Route to appropriate handler based on path
		path := r.URL.Path
		parts := strings.Split(strings.Trim(path, "/"), "/")

		if len(parts) == 1 && parts[0] == "checkpoints" {
			// GET /checkpoints - list all checkpoints
			s.handlers.HandleListCheckpoints(w, r)
		} else if len(parts) == 2 && parts[0] == "checkpoints" {
			// GET /checkpoints/{id} - get specific checkpoint
			s.handlers.HandleGetCheckpoint(w, r)
		} else if len(parts) == 3 && parts[0] == "checkpoints" && parts[2] == "restore" {
			// POST /checkpoints/{id}/restore - restore from checkpoint
			s.handlers.HandleCheckpointRestore(w, r)
		} else {
			http.NotFound(w, r)
		}
	}))

	// Register both exact and prefix patterns to handle all checkpoint routes
	mux.HandleFunc("/checkpoints", checkpointsHandler)
	mux.HandleFunc("/checkpoints/", checkpointsHandler)

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
		_, err := s.authManager.ExtractToken(r)
		if err != nil {
			s.logger.Debug("Authentication failed",
				"error", err,
				"path", r.URL.Path,
				"method", r.Method)
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
		_, err := s.authManager.ExtractAdminToken(r)
		if err != nil {
			s.logger.Debug("Admin authentication failed",
				"error", err,
				"path", r.URL.Path,
				"method", r.Method)
			if s.authManager.HasAdminToken() {
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
