package api

import (
	"context"
	"fmt"
	"log/slog"
	"net/http"
	"os"
	"strings"
	"time"

	"sprite-env/lib"
	"sprite-env/lib/api/exec"
	"sprite-env/lib/api/proxy"
	"sprite-env/lib/api/state"
)

// Server provides the HTTP API with authentication
type Server struct {
	server       *http.Server
	logger       *slog.Logger
	apiToken     string
	execHandler  *exec.Handler
	stateHandler *state.Handler
	proxyHandler *proxy.Handler
	config       *lib.ApplicationConfig
	systemState  state.SystemStateMachine
	stateMonitor *APIStateMonitor
	maxWaitTime  time.Duration
}

// NewServer creates a new API server
func NewServer(addr string, systemState state.SystemStateMachine, logger *slog.Logger, config *lib.ApplicationConfig) *Server {
	return NewServerWithMonitor(addr, systemState, logger, config, NewAPIStateMonitor())
}

// NewServerWithMonitor creates a new API server with a provided state monitor
func NewServerWithMonitor(addr string, systemState state.SystemStateMachine, logger *slog.Logger, config *lib.ApplicationConfig, stateMonitor *APIStateMonitor) *Server {
	// Use configured wait time or default to 30 seconds
	maxWaitTime := 30 * time.Second
	if config != nil && config.APIMaxWaitTime > 0 {
		maxWaitTime = config.APIMaxWaitTime
	}

	apiServer := &Server{
		logger:       logger,
		apiToken:     os.Getenv("SPRITE_HTTP_API_TOKEN"),
		execHandler:  exec.NewHandler(logger, config),
		stateHandler: state.NewHandler(systemState, logger),
		proxyHandler: proxy.NewHandler(logger),
		config:       config,
		systemState:  systemState,
		stateMonitor: stateMonitor,
		maxWaitTime:  maxWaitTime,
		server: &http.Server{
			Addr: addr,
		},
	}

	// Set up endpoints
	apiServer.setupEndpoints()

	return apiServer
}

// GetStateMonitor returns the state monitor for use in system state creation
func (s *Server) GetStateMonitor() lib.StateMonitor {
	return s.stateMonitor
}

// Start starts the API server in a background goroutine
func (s *Server) Start() error {
	if s.apiToken == "" {
		s.logger.Warn("SPRITE_HTTP_API_TOKEN not set, API authentication disabled")
	}

	s.logger.Info("Starting API server", "addr", s.server.Addr)

	go func() {
		if err := s.server.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			s.logger.Error("API server error", "error", err)
		}
	}()

	return nil
}

// Stop stops the API server gracefully
func (s *Server) Stop(ctx context.Context) error {
	s.logger.Info("Stopping API server")

	// Close the state monitor
	if s.stateMonitor != nil {
		s.stateMonitor.Close()
	}

	return s.server.Shutdown(ctx)
}

// setupEndpoints configures HTTP endpoints for the API
func (s *Server) setupEndpoints() {
	mux := http.NewServeMux()

	// Exec endpoint - waits for system to be running
	mux.Handle("/exec", s.waitForRunningMiddleware(s.authMiddleware(s.execHandler)))

	// State management endpoints - don't wait for running state (they might be used during startup)
	mux.HandleFunc("/checkpoint", s.authMiddleware(
		http.HandlerFunc(s.stateHandler.HandleCheckpoint)).ServeHTTP)
	mux.HandleFunc("/restore", s.authMiddleware(
		http.HandlerFunc(s.stateHandler.HandleRestore)).ServeHTTP)

	// Proxy endpoint - dedicated CONNECT proxy endpoint - waits for system to be running
	mux.Handle("/proxy", s.waitForRunningMiddleware(s.authMiddleware(s.proxyHandler)))

	s.server.Handler = mux
}

// waitForRunningMiddleware waits for the system to reach "Running" state before processing the request
func (s *Server) waitForRunningMiddleware(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		// Create a context with timeout
		ctx, cancel := context.WithTimeout(r.Context(), s.maxWaitTime)
		defer cancel()

		// Get current state for logging
		currentState := s.systemState.MustState().(string)

		s.logger.Debug("Request received",
			"currentState", currentState,
			"requestPath", r.URL.Path)

		// Wait for system to be ready
		startTime := time.Now()
		err := s.stateMonitor.WaitForReady(ctx)

		if err != nil {
			// Context was cancelled or timed out
			currentState = s.systemState.MustState().(string)

			if err == context.DeadlineExceeded {
				s.logger.Warn("Request timeout waiting for system to be ready",
					"currentState", currentState,
					"requestPath", r.URL.Path,
					"waitTime", time.Since(startTime))
				http.Error(w, fmt.Sprintf("System not ready (current state: %s)", currentState), http.StatusServiceUnavailable)
			} else {
				// Request was cancelled
				s.logger.Info("Request cancelled while waiting for system",
					"currentState", currentState,
					"requestPath", r.URL.Path,
					"waitTime", time.Since(startTime))
			}
			return
		}

		// System is ready, process the request
		waitTime := time.Since(startTime)
		if waitTime > 100*time.Millisecond {
			s.logger.Info("System became ready, processing request",
				"requestPath", r.URL.Path,
				"waitTime", waitTime)
		}

		next.ServeHTTP(w, r)
	})
}

// extractToken extracts authentication token from either fly-replay-src header or Authorization Bearer header
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

// authMiddleware checks for authentication token from either fly-replay-src or Authorization header
func (s *Server) authMiddleware(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		// Skip auth if no token is configured
		if s.apiToken == "" {
			next.ServeHTTP(w, r)
			return
		}

		token, err := s.extractToken(r)
		if err != nil {
			http.Error(w, "Missing or invalid authentication", http.StatusUnauthorized)
			return
		}

		if token != s.apiToken {
			http.Error(w, "Invalid authentication token", http.StatusUnauthorized)
			return
		}

		next.ServeHTTP(w, r)
	})
}

// SetMaxWaitTime sets the maximum time to wait for the system to be ready
func (s *Server) SetMaxWaitTime(duration time.Duration) {
	s.maxWaitTime = duration
}
