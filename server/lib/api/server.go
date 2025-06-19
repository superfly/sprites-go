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
	mux.Handle("/exec", s.waitForRunningMiddleware(s.authMiddleware(s.execHandler, "api")))

	// State management endpoints - don't wait for running state (they might be used during startup)
	mux.HandleFunc("/checkpoint", s.authMiddleware(
		http.HandlerFunc(s.stateHandler.HandleCheckpoint), "api").ServeHTTP)
	mux.HandleFunc("/restore", s.authMiddleware(
		http.HandlerFunc(s.stateHandler.HandleRestore), "api").ServeHTTP)

	// Proxy endpoint - matches all paths - waits for system to be running
	mux.Handle("/", s.waitForRunningMiddleware(s.authMiddleware(s.proxyHandler, "proxy")))

	s.server.Handler = mux
}

// waitForRunningMiddleware waits for the system to reach "Running" state before processing the request
func (s *Server) waitForRunningMiddleware(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		// Create a context with 30 second timeout
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

// parseReplayState parses the fly-replay-src header value
// Format: "key1=value1;key2=value2;state=<mode>:<token>"
func parseReplayState(headerValue string) (token string, mode string, stateValue string, err error) {
	// First, parse the semicolon-separated key-value pairs
	parts := strings.Split(headerValue, ";")
	stateValue = ""

	for _, part := range parts {
		kv := strings.SplitN(strings.TrimSpace(part), "=", 2)
		if len(kv) != 2 {
			continue
		}
		key := strings.TrimSpace(kv[0])
		value := kv[1] // Don't trim the value here to preserve it exactly

		if key == "state" {
			stateValue = value
			break
		}
	}

	if stateValue == "" {
		return "", "", "", fmt.Errorf("missing state in fly-replay-src header")
	}

	// Parse state value expecting format: "mode:token" or "mode:token:extra"
	// Trim spaces from state value for parsing
	trimmedState := strings.TrimSpace(stateValue)
	stateParts := strings.SplitN(trimmedState, ":", 2)
	if len(stateParts) != 2 {
		return "", "", "", fmt.Errorf("invalid state format, expected 'mode:token'")
	}

	mode = strings.TrimSpace(stateParts[0])
	token = strings.TrimSpace(stateParts[1])

	if token == "" {
		return "", "", "", fmt.Errorf("missing token in state")
	}
	if mode == "" {
		return "", "", "", fmt.Errorf("missing mode in state")
	}

	// For the returned stateValue, reconstruct it without extra spaces
	stateValue = mode + ":" + token

	return token, mode, stateValue, nil
}

// authMiddleware checks the fly-replay-src header for authentication
func (s *Server) authMiddleware(next http.Handler, requiredMode string) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		replayHeader := r.Header.Get("fly-replay-src")
		if replayHeader == "" {
			http.Error(w, "Missing fly-replay-src header", http.StatusUnauthorized)
			return
		}

		token, mode, stateValue, err := parseReplayState(replayHeader)
		if err != nil {
			http.Error(w, fmt.Sprintf("Invalid replay state: %v", err), http.StatusBadRequest)
			return
		}

		// Check authentication token if configured
		if s.apiToken != "" {
			// For proxy mode, extract the actual token (format: proxy:token:port)
			authToken := token
			if mode == "proxy" {
				// Split to get just the token part
				parts := strings.SplitN(token, ":", 2)
				if len(parts) > 0 {
					authToken = parts[0]
				}
			}

			if authToken != s.apiToken {
				http.Error(w, "Invalid authentication token", http.StatusUnauthorized)
				return
			}
		}

		// Check if the mode matches what this endpoint expects
		if requiredMode != "" && mode != requiredMode {
			if mode == "proxy" && requiredMode != "proxy" {
				// Proxy mode trying to access non-proxy endpoint
				http.Error(w, "This endpoint is not available in proxy mode", http.StatusNotFound)
				return
			}
			if mode == "api" && requiredMode == "proxy" {
				// API mode trying to access proxy endpoint
				http.Error(w, "Not found", http.StatusNotFound)
				return
			}
		}

		// Pass along state value in context for handlers
		ctx := context.WithValue(r.Context(), "mode", mode)
		ctx = context.WithValue(ctx, "stateValue", stateValue)
		r = r.WithContext(ctx)

		next.ServeHTTP(w, r)
	})
}

// SetMaxWaitTime sets the maximum time to wait for the system to be ready
func (s *Server) SetMaxWaitTime(duration time.Duration) {
	s.maxWaitTime = duration
}
