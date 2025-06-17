package state

import (
	"encoding/json"
	"fmt"
	"log/slog"
	"net/http"
)

// SystemStateMachine interface defines what we need from the system state machine
type SystemStateMachine interface {
	MustState() interface{}
	Fire(trigger string, args ...any) error
}

// CheckpointRequest represents the request body for /checkpoint endpoint
type CheckpointRequest struct {
	CheckpointID string `json:"checkpoint_id"`
}

// RestoreRequest represents the request body for /restore endpoint
type RestoreRequest struct {
	CheckpointID string `json:"checkpoint_id"`
}

// Handler handles state management endpoints (checkpoint, restore)
type Handler struct {
	systemState SystemStateMachine
	logger      *slog.Logger
}

// NewHandler creates a new state handler
func NewHandler(systemState SystemStateMachine, logger *slog.Logger) *Handler {
	return &Handler{
		systemState: systemState,
		logger:      logger,
	}
}

// HandleCheckpoint handles the /checkpoint endpoint
func (h *Handler) HandleCheckpoint(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	var req CheckpointRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, fmt.Sprintf("Invalid request body: %v", err), http.StatusBadRequest)
		return
	}

	if req.CheckpointID == "" {
		http.Error(w, "checkpoint_id is required", http.StatusBadRequest)
		return
	}

	// Trigger checkpoint with the provided ID
	if err := h.systemState.Fire("CheckpointRequested", req.CheckpointID); err != nil {
		h.logger.Error("Failed to start checkpoint", "error", err, "checkpointID", req.CheckpointID)
		http.Error(w, fmt.Sprintf("Failed to start checkpoint: %v", err), http.StatusInternalServerError)
		return
	}

	h.logger.Info("Checkpoint initiated via API", "checkpointID", req.CheckpointID)
	w.WriteHeader(http.StatusAccepted)
	json.NewEncoder(w).Encode(map[string]string{
		"status":        "checkpoint initiated",
		"checkpoint_id": req.CheckpointID,
	})
}

// HandleRestore handles the /restore endpoint
func (h *Handler) HandleRestore(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	var req RestoreRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, fmt.Sprintf("Invalid request body: %v", err), http.StatusBadRequest)
		return
	}

	if req.CheckpointID == "" {
		http.Error(w, "checkpoint_id is required", http.StatusBadRequest)
		return
	}

	// Trigger restore with the provided ID
	if err := h.systemState.Fire("RestoreRequested", req.CheckpointID); err != nil {
		h.logger.Error("Failed to start restore", "error", err, "checkpointID", req.CheckpointID)
		http.Error(w, fmt.Sprintf("Failed to start restore: %v", err), http.StatusInternalServerError)
		return
	}

	h.logger.Info("Restore initiated via API", "checkpointID", req.CheckpointID)
	w.WriteHeader(http.StatusAccepted)
	json.NewEncoder(w).Encode(map[string]string{
		"status":        "restore initiated",
		"checkpoint_id": req.CheckpointID,
	})
}
