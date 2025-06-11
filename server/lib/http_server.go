package lib

import (
	"context"
	"encoding/json"
	"fmt"
	"log/slog"
	"net/http"
)

// HTTPServer provides monitoring endpoints for the system
type HTTPServer struct {
	server             *http.Server
	systemStateMachine *SystemState
	logger             *slog.Logger
}

// NewHTTPServer creates a new HTTP server for monitoring
func NewHTTPServer(addr string, systemStateMachine *SystemState, logger *slog.Logger) *HTTPServer {
	httpServer := &HTTPServer{
		systemStateMachine: systemStateMachine,
		logger:             logger,
		server: &http.Server{
			Addr: addr,
		},
	}

	// Set up endpoints
	httpServer.setupEndpoints()

	return httpServer
}

// Start starts the HTTP server in a background goroutine
func (h *HTTPServer) Start() error {
	h.logger.Info("Starting HTTP server", "addr", h.server.Addr)

	go func() {
		if err := h.server.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			h.logger.Error("HTTP server error", "error", err)
		}
	}()

	return nil
}

// Stop stops the HTTP server gracefully
func (h *HTTPServer) Stop(ctx context.Context) error {
	h.logger.Info("Stopping HTTP server")
	return h.server.Shutdown(ctx)
}

// setupEndpoints configures HTTP endpoints for monitoring
func (h *HTTPServer) setupEndpoints() {
	mux := http.NewServeMux()

	// Current state endpoint
	mux.HandleFunc("/state", h.handleState)

	// Health check endpoint
	mux.HandleFunc("/health", h.handleHealth)

	// Checkpoint endpoint
	mux.HandleFunc("/checkpoint", h.handleCheckpoint)

	// Restore endpoint
	mux.HandleFunc("/restore", h.handleRestore)

	h.server.Handler = mux
}

// handleState returns the current system state
func (h *HTTPServer) handleState(w http.ResponseWriter, r *http.Request) {
	state := map[string]interface{}{
		"system":    h.systemStateMachine.GetState(),
		"errorType": h.systemStateMachine.GetErrorType(),
	}
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(state)
}

// handleHealth returns health check information
func (h *HTTPServer) handleHealth(w http.ResponseWriter, r *http.Request) {
	systemState := h.systemStateMachine.GetState()
	health := map[string]interface{}{
		"status":  "ok",
		"running": systemState == SystemStateRunning,
		"state":   systemState,
	}
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(health)
}

// handleCheckpoint initiates a checkpoint operation
func (h *HTTPServer) handleCheckpoint(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	if err := h.systemStateMachine.Fire(SystemTriggerCheckpointRequested); err != nil {
		h.logger.Error("Failed to start checkpoint", "error", err)
		http.Error(w, fmt.Sprintf("Failed to start checkpoint: %v", err), http.StatusInternalServerError)
		return
	}

	h.logger.Info("Checkpoint initiated via HTTP")
	w.WriteHeader(http.StatusAccepted)
	json.NewEncoder(w).Encode(map[string]string{"status": "checkpoint initiated"})
}

// handleRestore initiates a restore operation
func (h *HTTPServer) handleRestore(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	if err := h.systemStateMachine.Fire(SystemTriggerRestoreRequested); err != nil {
		h.logger.Error("Failed to start restore", "error", err)
		http.Error(w, fmt.Sprintf("Failed to start restore: %v", err), http.StatusInternalServerError)
		return
	}

	h.logger.Info("Restore initiated via HTTP")
	w.WriteHeader(http.StatusAccepted)
	json.NewEncoder(w).Encode(map[string]string{"status": "restore initiated"})
}
