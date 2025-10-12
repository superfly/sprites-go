package api

import (
	"context"
	"errors"
	"fmt"
	"log/slog"
	"net/http"
	"strings"
	"time"

	"github.com/superfly/sprite-env/pkg/sync"
	"github.com/superfly/sprite-env/pkg/tap"
	"github.com/superfly/sprite-env/pkg/terminal"
)

var (
	ErrNoAuth = errors.New("API token must be set - server cannot run without authentication")
)

// Server provides the HTTP API with authentication
type Server struct {
	server          *http.Server
	logger          *slog.Logger
	config          Config
	handlers        *Handlers
	system          SystemManager
	syncServer      *sync.Server
	authManager     *AuthManager
	contextEnricher ContextEnricher
	activityObs     func(start bool)
	proxyHandler    *ProxyHandler
}

// NewServer creates a new API server
func NewServer(config Config, system SystemManager, ctx context.Context) (*Server, error) {
	logger := tap.Logger(ctx)
	if config.APIToken == "" {
		return nil, ErrNoAuth
	}

	if config.MaxWaitTime == 0 {
		config.MaxWaitTime = 30 * time.Second
	}

	// Create handlers config
	handlersConfig := HandlerConfig{
		MaxWaitTime:        config.MaxWaitTime,
		ExecWrapperCommand: config.ExecWrapperCommand,
		ProxyLocalhostIPv4: config.ProxyLocalhostIPv4,
		ProxyLocalhostIPv6: config.ProxyLocalhostIPv6,
		TMUXManager:        config.TMUXManager,
	}

	// Create handlers
	h := NewHandlers(ctx, system, handlersConfig)

	// Create sync server
	syncConfig := sync.ServerConfig{
		TargetBasePath: config.SyncTargetPath,
		MaxConnections: 10,
		Logger:         logger,
	}
	syncServer := sync.NewServer(syncConfig)

	// Create auth manager
	authManager := NewAuthManager(config.APIToken, config.AdminToken)

	// Create proxy handler for proxy:: prefixed tokens
	// Try IPv6 (fd00:...) first, then fall back to IPv4 (10.0.0.1)
	proxyHandler := NewProxyHandler(logger, "fd00::2", "10.0.0.1", 8080)

	s := &Server{
		logger:       logger,
		config:       config,
		handlers:     h,
		system:       system,
		syncServer:   syncServer,
		authManager:  authManager,
		proxyHandler: proxyHandler,
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

	// Add global auth middleware - this handles both authentication and proxy routing
	{
		next := handler
		handler = http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			_, isProxy, err := s.authManager.ExtractTokenWithProxyCheck(r)
			if err != nil {
				s.logger.Debug("Authentication failed",
					"error", err,
					"path", r.URL.Path,
					"method", r.Method)
				http.Error(w, "Missing or invalid authentication", http.StatusUnauthorized)
				return
			}

			// If it's a proxy token, route to proxy handler
			if isProxy {
				// Tag the context with proxy info for the default HTTP logger
				ctx := context.WithValue(r.Context(), proxyInfoKey{}, "proxy")
				r = r.WithContext(ctx)

				s.proxyHandler.ServeHTTP(w, r)
				return
			}

			// Otherwise, continue with normal handling
			next.ServeHTTP(w, r)
		})
	}

	{
		next := handler
		handler = http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			if s.activityObs != nil {
				s.activityObs(true)
				defer s.activityObs(false)
			}
			next.ServeHTTP(w, r)
		})
	}

	// Add global overlay wait middleware
	{
		next := handler
		handler = http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			// Wait for overlay to be ready before processing any request
			ctx, cancel := context.WithTimeout(r.Context(), s.config.MaxWaitTime)
			defer cancel()

			startTime := time.Now()
			err := s.system.WhenStorageReady(ctx)
			waitTime := time.Since(startTime)

			if err != nil {
				s.logger.Warn("Request timeout waiting for overlay to be ready",
					"requestPath", r.URL.Path,
					"waitTime", waitTime,
					"error", err)
				http.Error(w, "Storage not ready", http.StatusServiceUnavailable)
				return
			}

			// Log if we waited more than 5ms (i.e., we held the request)
			if waitTime > 5*time.Millisecond {
				s.logger.Info("Held request while waiting for overlay to be ready",
					"requestPath", r.URL.Path,
					"waitTime", waitTime)
			}

			next.ServeHTTP(w, r)
		})
	}

	s.server = &http.Server{
		Addr: config.ListenAddr,
		Handler: http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			// Check if this is a proxy request and include that in the log
			if proxyInfo := r.Context().Value(proxyInfoKey{}); proxyInfo != nil {
				s.logger.Info("request", "url", r.URL.String(), "type", proxyInfo)
			} else {
				s.logger.Info("request", "url", r.URL.String())
			}
			handler.ServeHTTP(w, r)
		}),
	}

	return s, nil
}

// SetAdminChannel sets the admin channel for context enrichment
func (s *Server) SetAdminChannel(enricher ContextEnricher) {
	s.contextEnricher = enricher
}

// SetTMUXManager sets the TMUX manager on the handlers
func (s *Server) SetTMUXManager(tmuxManager *terminal.TMUXManager) {
	if s.handlers != nil {
		s.handlers.SetTMUXManager(tmuxManager)
	}
}

// SetActivityObserver sets a callback to observe request start/end
func (s *Server) SetActivityObserver(observe func(start bool)) {
	s.activityObs = observe
}

// setupEndpoints configures HTTP endpoints for the API
func (s *Server) setupEndpoints(mux *http.ServeMux) {
	// Note: All endpoints have global authentication applied at the top level

	// Exec endpoint - waits for process to be running
	mux.HandleFunc("/exec", s.enrichContextMiddleware(s.waitForProcessMiddleware(s.handlers.HandleExec)))

	mux.HandleFunc("/sync", s.waitForProcessMiddleware(s.syncServer.HandleWebSocket))

	// Checkpoint endpoint - waits for storage to be ready
	mux.HandleFunc("/checkpoint", s.waitForStorageMiddleware(s.handlers.HandleCheckpoint))

	// Checkpoint management endpoints - wait for storage to be ready
	// This pattern matches /checkpoints and any subpaths like /checkpoints/{id} or /checkpoints/{id}/restore
	checkpointsHandler := s.waitForStorageMiddleware(func(w http.ResponseWriter, r *http.Request) {
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
	})

	// Register both exact and prefix patterns to handle all checkpoint routes
	mux.HandleFunc("/checkpoints", checkpointsHandler)
	mux.HandleFunc("/checkpoints/", checkpointsHandler)

	// Proxy endpoint - waits for process to be running
	mux.HandleFunc("/proxy", s.enrichContextMiddleware(s.waitForProcessMiddleware(s.handlers.HandleProxy)))

	// Suspend endpoint - wait for storage to be ready
	mux.HandleFunc("/suspend", s.waitForStorageMiddleware(s.handlers.HandleSuspend))

	// Debug endpoints - don't wait for process or JuiceFS
	mux.HandleFunc("/debug/create-zombie", s.handlers.HandleDebugCreateZombie)
	mux.HandleFunc("/debug/check-process", s.handlers.HandleDebugCheckProcess)

	// Admin endpoints
	mux.HandleFunc("/admin/reset-state", s.handlers.HandleAdminResetState)

	// Sprite environment endpoint - POST /v1/sprites/:name/environment
	// Waits for storage to be ready (needs JuiceFS for sprite.db)
	mux.HandleFunc("/v1/sprites/", s.waitForStorageMiddleware(func(w http.ResponseWriter, r *http.Request) {
		// Only handle paths matching /v1/sprites/:name/environment
		parts := strings.Split(strings.Trim(r.URL.Path, "/"), "/")
		if len(parts) == 4 && parts[0] == "v1" && parts[1] == "sprites" && parts[3] == "environment" {
			s.handlers.HandleSetSpriteEnvironment(w, r)
		} else {
			http.NotFound(w, r)
		}
	}))
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

// contextEnricherKey is the key for storing the enricher in context
type contextEnricherKey struct{}

// proxyInfoKey is the key for storing proxy information in context
type proxyInfoKey struct{}

// enrichContextMiddleware enriches the request context if a context enricher is configured
func (s *Server) enrichContextMiddleware(next http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if s.contextEnricher != nil {
			// Enrich the context with admin channel data
			ctx := s.contextEnricher.EnrichContext(r.Context())
			// Also store the enricher itself in context for handlers to use
			ctx = context.WithValue(ctx, contextEnricherKey{}, s.contextEnricher)
			r = r.WithContext(ctx)
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
		err := s.system.WhenProcessRunning(ctx)
		waitTime := time.Since(startTime)

		if err != nil {
			s.logger.Warn("Request timeout waiting for process to be running",
				"requestPath", r.URL.Path,
				"waitTime", waitTime,
				"error", err,
				"maxWaitTime", s.config.MaxWaitTime,
				"isProcessRunning", s.system.IsProcessRunning())

			// Provide more detailed error message
			errMsg := fmt.Sprintf("Process not ready after %v (max wait: %v). Process running: %v. Error: %v",
				waitTime.Round(time.Millisecond),
				s.config.MaxWaitTime,
				s.system.IsProcessRunning(),
				err)
			http.Error(w, errMsg, http.StatusServiceUnavailable)
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

// waitForStorageMiddleware waits for storage (overlay) to be ready before handling the request
func (s *Server) waitForStorageMiddleware(next http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		ctx, cancel := context.WithTimeout(r.Context(), s.config.MaxWaitTime)
		defer cancel()

		startTime := time.Now()

		// Use efficient waiting for storage (JuiceFS and overlay)
		err := s.system.WhenStorageReady(ctx)
		waitTime := time.Since(startTime)

		if err != nil {
			s.logger.Warn("Request timeout waiting for overlay to be ready",
				"requestPath", r.URL.Path,
				"waitTime", waitTime,
				"error", err)
			http.Error(w, "Storage not ready", http.StatusServiceUnavailable)
			return
		}

		// Log if we waited more than 5ms
		if waitTime > 5*time.Millisecond {
			s.logger.Info("Overlay became ready, processing request",
				"requestPath", r.URL.Path,
				"waitTime", waitTime)
		}

		next(w, r)
	}
}

// GetTMUXManager returns the TMUX manager from the handlers
func (s *Server) GetTMUXManager() *terminal.TMUXManager {
	if s.handlers != nil {
		return s.handlers.GetTMUXManager()
	}
	return nil
}

// authMiddleware wraps an http.Handler with authentication
// This is exposed for testing purposes
func (s *Server) authMiddleware(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		_, isProxy, err := s.authManager.ExtractTokenWithProxyCheck(r)
		if err != nil {
			s.logger.Debug("Authentication failed",
				"error", err,
				"path", r.URL.Path,
				"method", r.Method)
			http.Error(w, "Missing or invalid authentication", http.StatusUnauthorized)
			return
		}

		// If it's a proxy token, route to proxy handler
		if isProxy {
			// Tag the context with proxy info for the default HTTP logger
			ctx := context.WithValue(r.Context(), proxyInfoKey{}, "proxy")
			r = r.WithContext(ctx)

			s.proxyHandler.ServeHTTP(w, r)
			return
		}

		// Otherwise, continue with normal handling
		next.ServeHTTP(w, r)
	})
}
