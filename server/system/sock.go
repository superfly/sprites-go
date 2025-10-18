package system

import (
	"context"
	"encoding/json"
	"fmt"
	"net"
	"net/http"
	"os"
	"path/filepath"
	"time"

	libapi "github.com/superfly/sprite-env/lib/api"
	"github.com/superfly/sprite-env/pkg/tap"
	"github.com/superfly/sprite-env/server/api"
)

// SockServer handles the Unix socket API for service management
type SockServer struct {
	system      *System
	apiHandlers *api.Handlers // Reuse API handlers for checkpoint endpoints
	listener    net.Listener
	server      *http.Server
	ctx         context.Context
	logDir      string // Base directory for service logs
}

// NewSockServer creates a new Unix socket server
func NewSockServer(ctx context.Context, system *System, logDir string) (*SockServer, error) {
	// Create API handlers to reuse checkpoint and service endpoint logic
	handlersConfig := api.HandlerConfig{
		MaxWaitTime:        30 * time.Second,
		ContainerEnabled:   system.config.ContainerEnabled,
		ProxyLocalhostIPv4: system.config.ProxyLocalhostIPv4,
		ProxyLocalhostIPv6: system.config.ProxyLocalhostIPv6,
	}
	apiHandlers := api.NewHandlers(ctx, system, handlersConfig)

	return &SockServer{
		system:      system,
		apiHandlers: apiHandlers,
		ctx:         ctx,
		logDir:      logDir,
	}, nil
}

// Start starts the Unix socket server
func (s *SockServer) Start(socketPath string) error {
	// Remove existing socket if it exists
	if err := os.RemoveAll(socketPath); err != nil {
		return fmt.Errorf("failed to remove existing socket: %w", err)
	}

	// Ensure directory exists
	if err := os.MkdirAll(filepath.Dir(socketPath), 0755); err != nil {
		return fmt.Errorf("failed to create socket directory: %w", err)
	}

	// Create Unix socket listener
	listener, err := net.Listen("unix", socketPath)
	if err != nil {
		return fmt.Errorf("failed to create unix socket: %w", err)
	}
	s.listener = listener

	// Set socket permissions
	if err := os.Chmod(socketPath, 0666); err != nil {
		listener.Close()
		return fmt.Errorf("failed to set socket permissions: %w", err)
	}

	// Create HTTP server with routes
	mux := http.NewServeMux()
	s.setupRoutes(mux)

	s.server = &http.Server{
		Handler:     mux,
		ReadTimeout: 30 * time.Second,
	}

	// Start serving
	go func() {
		if err := s.server.Serve(listener); err != nil && err != http.ErrServerClosed {
			tap.Logger(s.ctx).Error("socket server error", "error", err)
		}
	}()

	tap.Logger(s.ctx).Info("services API socket server started", "path", socketPath)
	return nil
}

// Stop stops the Unix socket server
func (s *SockServer) Stop() error {
	if s.server != nil {
		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		defer cancel()
		if err := s.server.Shutdown(ctx); err != nil {
			return fmt.Errorf("failed to shutdown server: %w", err)
		}
	}

	return nil
}

func (s *SockServer) setupRoutes(mux *http.ServeMux) {
	// Service endpoints (no auth required) - use API handlers
	mux.HandleFunc("GET /v1/services", s.apiHandlers.HandleListServices)
	mux.HandleFunc("PUT /v1/services/{name}", s.apiHandlers.HandleCreateService)
	mux.HandleFunc("GET /v1/services/{name}", s.apiHandlers.HandleGetService)
	mux.HandleFunc("DELETE /v1/services/{name}", s.apiHandlers.HandleDeleteService)
	mux.HandleFunc("POST /v1/services/{name}/start", s.apiHandlers.HandleStartService)
	mux.HandleFunc("POST /v1/services/{name}/stop", s.apiHandlers.HandleStopService)
	mux.HandleFunc("POST /v1/services/signal", s.apiHandlers.HandleSignalService)

	// Checkpoint endpoints (no auth required)
	mux.HandleFunc("GET /v1/checkpoints", s.apiHandlers.HandleListCheckpoints)
	mux.HandleFunc("GET /v1/checkpoints/{id}", s.apiHandlers.HandleGetCheckpoint)
	// Restore needs custom handling - returns immediately then triggers restore
	mux.HandleFunc("POST /v1/checkpoints/{id}/restore", s.handleRestoreCheckpoint)
	mux.HandleFunc("POST /v1/checkpoint", s.apiHandlers.HandleCheckpoint)
}

// handleRestoreCheckpoint handles restore differently than the API version
// It returns immediately with a success response, then triggers the restore asynchronously
// This is necessary because restore shuts down the environment the caller is running in
func (s *SockServer) handleRestoreCheckpoint(w http.ResponseWriter, r *http.Request) {
	checkpointID := r.PathValue("id")
	if checkpointID == "" {
		http.Error(w, "checkpoint id required", http.StatusBadRequest)
		return
	}

	tap.Logger(s.ctx).Info("Restore request (async)", "checkpoint_id", checkpointID)

	// Immediately return success response
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusAccepted)

	response := map[string]string{
		"status":        "accepted",
		"checkpoint_id": checkpointID,
		"message":       "Restore initiated. Environment will restart shortly.",
	}
	json.NewEncoder(w).Encode(response)

	// Trigger restore asynchronously after response is sent
	go func() {
		// Small delay to ensure response is sent
		time.Sleep(100 * time.Millisecond)

		ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
		defer cancel()

		// Create a channel for streaming (but we won't use it for the client)
		streamCh := make(chan libapi.StreamMessage, 10)

		// Log stream messages to the system logger instead of sending to client
		go func() {
			for msg := range streamCh {
				tap.Logger(s.ctx).Info("Restore progress",
					"type", msg.Type,
					"data", msg.Data,
					"error", msg.Error)
			}
		}()

		// Perform restore
		err := s.system.RestoreWithStream(ctx, checkpointID, streamCh)
		if err != nil {
			tap.Logger(s.ctx).Error("Restore failed", "error", err, "checkpoint_id", checkpointID)
		} else {
			tap.Logger(s.ctx).Info("Restore completed", "checkpoint_id", checkpointID)
		}
	}()
}
