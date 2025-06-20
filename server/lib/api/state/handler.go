package state

import (
	"encoding/json"
	"fmt"
	"log/slog"
	"net/http"
	"time"

	"sprite-env/lib/managers"
)

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
	processState   *managers.ProcessState
	componentState *managers.ComponentState
	logger         *slog.Logger
}

// NewHandler creates a new state handler
func NewHandler(processState *managers.ProcessState, logger *slog.Logger) *Handler {
	return &Handler{
		processState: processState,
		logger:       logger,
	}
}

// SetComponentState sets the component state manager (if available)
func (h *Handler) SetComponentState(componentState *managers.ComponentState) {
	h.componentState = componentState
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

	// If we have a component, trigger checkpoint on it
	if h.componentState != nil {
		if err := h.componentState.Fire("Checkpointing", req.CheckpointID); err != nil {
			h.logger.Error("Failed to start checkpoint", "error", err, "checkpointID", req.CheckpointID)
			http.Error(w, fmt.Sprintf("Failed to start checkpoint: %v", err), http.StatusInternalServerError)
			return
		}
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

	// Start restore process in a goroutine to avoid blocking the API response
	go h.performRestore(req.CheckpointID)

	h.logger.Info("Restore initiated via API", "checkpointID", req.CheckpointID)
	w.WriteHeader(http.StatusAccepted)
	json.NewEncoder(w).Encode(map[string]string{
		"status":        "restore initiated",
		"checkpoint_id": req.CheckpointID,
	})
}

// performRestore handles the restore sequence: stop process, wait for stop, restore, start process
func (h *Handler) performRestore(checkpointID string) {
	h.logger.Info("Starting restore sequence", "checkpointID", checkpointID)

	// Step 1: Stop the process if it's running
	if h.processState != nil {
		currentState := h.processState.MustState().(string)
		if currentState == "Running" {
			h.logger.Info("Stopping process for restore")
			if err := h.processState.Fire("Stopping"); err != nil {
				h.logger.Error("Failed to stop process for restore", "error", err)
				return
			}

			// Wait for process to stop (with timeout)
			timeout := time.After(30 * time.Second)
			ticker := time.NewTicker(100 * time.Millisecond)
			defer ticker.Stop()

			for {
				select {
				case <-timeout:
					h.logger.Error("Timeout waiting for process to stop")
					return
				case <-ticker.C:
					state := h.processState.MustState().(string)
					if state == "Stopped" {
						h.logger.Info("Process stopped successfully")
						break
					}
				}
				break
			}
		}
	}

	// Step 2: Perform restore on component
	if h.componentState != nil {
		h.logger.Info("Restoring component", "checkpointID", checkpointID)
		if err := h.componentState.Fire("Restoring", checkpointID); err != nil {
			h.logger.Error("Failed to restore component", "error", err)
			return
		}

		// Wait for restore to complete (with timeout)
		timeout := time.After(60 * time.Second)
		ticker := time.NewTicker(100 * time.Millisecond)
		defer ticker.Stop()

		for {
			select {
			case <-timeout:
				h.logger.Error("Timeout waiting for restore to complete")
				return
			case <-ticker.C:
				state := h.componentState.MustState().(string)
				if state == "Running" {
					h.logger.Info("Component restored successfully")
					break
				} else if state == "Error" {
					h.logger.Error("Component restore failed")
					return
				}
			}
			break
		}
	}

	// Step 3: Start the process back up
	if h.processState != nil {
		h.logger.Info("Starting process after restore")
		if err := h.processState.Fire("Starting"); err != nil {
			h.logger.Error("Failed to start process after restore", "error", err)
			return
		}
	}

	h.logger.Info("Restore sequence completed", "checkpointID", checkpointID)
}
