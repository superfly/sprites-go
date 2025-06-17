package api

import (
	"context"
	"fmt"
	"log/slog"
	"net/http"
	"os"
	"strings"

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
}

// NewServer creates a new API server
func NewServer(addr string, systemState state.SystemStateMachine, logger *slog.Logger) *Server {
	apiServer := &Server{
		logger:       logger,
		apiToken:     os.Getenv("SPRITE_HTTP_API_TOKEN"),
		execHandler:  exec.NewHandler(logger),
		stateHandler: state.NewHandler(systemState, logger),
		proxyHandler: proxy.NewHandler(logger),
		server: &http.Server{
			Addr: addr,
		},
	}

	// Set up endpoints
	apiServer.setupEndpoints()

	return apiServer
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
	return s.server.Shutdown(ctx)
}

// setupEndpoints configures HTTP endpoints for the API
func (s *Server) setupEndpoints() {
	mux := http.NewServeMux()

	// Exec endpoint
	mux.Handle("/exec", s.authMiddleware(s.execHandler, "api"))

	// State management endpoints
	mux.HandleFunc("/checkpoint", s.authMiddleware(
		http.HandlerFunc(s.stateHandler.HandleCheckpoint), "api").ServeHTTP)
	mux.HandleFunc("/restore", s.authMiddleware(
		http.HandlerFunc(s.stateHandler.HandleRestore), "api").ServeHTTP)

	// Proxy endpoint - matches all paths
	mux.Handle("/", s.authMiddleware(s.proxyHandler, "proxy"))

	s.server.Handler = mux
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
