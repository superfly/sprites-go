package api

import (
	"context"
	"errors"
	"fmt"
	"log/slog"
	"net/http"
	"strings"
	"time"

	"spritectl/api/handlers"
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
		MaxWaitTime:           config.MaxWaitTime,
		ExecWrapperCommand:    config.ExecWrapperCommand,
		ExecTTYWrapperCommand: config.ExecTTYWrapperCommand,
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

	s.server = &http.Server{
		Addr:    config.ListenAddr,
		Handler: mux,
	}

	return s, nil
}

// setupEndpoints configures HTTP endpoints for the API
func (s *Server) setupEndpoints(mux *http.ServeMux) {
	// All endpoints require authentication

	// Docker-compatible exec endpoints
	// Pattern: /containers/{id}/exec for create
	// Pattern: /exec/{id}/start for start
	// Pattern: /exec/{id}/json for inspect
	mux.HandleFunc("/containers/", s.authMiddleware(s.waitForRunningMiddleware(func(w http.ResponseWriter, r *http.Request) {
		// Parse path: /containers/{containerID}/exec
		parts := strings.Split(strings.Trim(r.URL.Path, "/"), "/")
		if len(parts) == 3 && parts[2] == "exec" && r.Method == http.MethodPost {
			// Container ID is in parts[1], but we ignore it since we only have one container
			s.handlers.HandleDockerExecCreate(w, r)
		} else {
			http.NotFound(w, r)
		}
	})))

	mux.HandleFunc("/exec/", s.authMiddleware(s.waitForRunningMiddleware(func(w http.ResponseWriter, r *http.Request) {
		// Parse path: /exec/{execID}/start or /exec/{execID}/json
		path := r.URL.Path
		parts := strings.Split(strings.Trim(path, "/"), "/")

		if len(parts) == 3 {
			if parts[2] == "start" {
				s.handlers.HandleDockerExecStart(w, r)
			} else if parts[2] == "json" {
				s.handlers.HandleDockerExecInspect(w, r)
			} else {
				http.NotFound(w, r)
			}
		} else {
			http.NotFound(w, r)
		}
	})))

	// State management endpoints - don't wait for running state
	mux.HandleFunc("/checkpoint", s.authMiddleware(s.handlers.HandleCheckpoint))

	// Checkpoint management endpoints
	mux.HandleFunc("/checkpoints/", s.authMiddleware(func(w http.ResponseWriter, r *http.Request) {
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
	}))

	// Proxy endpoint - waits for process to be running
	mux.HandleFunc("/proxy", s.authMiddleware(s.waitForRunningMiddleware(s.handlers.HandleProxy)))

	// Debug endpoints - require auth but don't wait for process
	mux.HandleFunc("/debug/create-zombie", s.authMiddleware(s.handlers.HandleDebugCreateZombie))
	mux.HandleFunc("/debug/check-process", s.authMiddleware(s.handlers.HandleDebugCheckProcess))
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

// waitForRunningMiddleware waits for the process to be running before handling the request
func (s *Server) waitForRunningMiddleware(next http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		ctx, cancel := context.WithTimeout(r.Context(), s.config.MaxWaitTime)
		defer cancel()

		ticker := time.NewTicker(100 * time.Millisecond)
		defer ticker.Stop()

		startTime := time.Now()

		for {
			select {
			case <-ctx.Done():
				s.logger.Warn("Request timeout waiting for process to be running",
					"requestPath", r.URL.Path,
					"waitTime", time.Since(startTime))
				http.Error(w, "Process not ready", http.StatusServiceUnavailable)
				return

			case <-ticker.C:
				if s.system.IsProcessRunning() {
					waitTime := time.Since(startTime)
					if waitTime > 100*time.Millisecond {
						s.logger.Info("Process became ready, processing request",
							"requestPath", r.URL.Path,
							"waitTime", waitTime)
					}
					next(w, r)
					return
				}
			}
		}
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
