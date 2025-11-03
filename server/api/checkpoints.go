package api

import (
	"context"
	"encoding/json"
	"fmt"
	"net/http"
	"strings"
	"time"

	"github.com/superfly/sprite-env/lib/api"
)

// HandleListCheckpoints handles GET /sprites/{id}/checkpoints
// @public
// @operation GET /v1/sprites/{id}/checkpoints
// @summary List sprite checkpoints
// @description Retrieve a list of all available checkpoints for a specific sprite
// @tags Sprites
// @security Bearer
// @param id path string true "Sprite ID"
// @param history query string false "Filter checkpoints by history version"
// @response 200 {array} string "List of checkpoints"
// @response 401 {string} string "Unauthorized - invalid or missing authentication"
// @response 500 {string} string "Internal server error"
// @response 503 {string} string "Service unavailable - JuiceFS not configured"
func (h *Handlers) HandleListCheckpoints(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodGet {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	// Storage readiness will be checked by the actual operations

	ctx := r.Context()

	// Check for history filter query parameter
	historyVersion := r.URL.Query().Get("history")
	if historyVersion != "" {
		// Return grep-style results for checkpoints with this version in history
		results, err := h.system.ListCheckpointsByHistory(ctx, historyVersion)
		if err != nil {
			h.logger.Error("Failed to list checkpoints by history", "error", err, "version", historyVersion)
			http.Error(w, fmt.Sprintf("Failed to list checkpoints: %v", err), http.StatusInternalServerError)
			return
		}

		// Return as simple text output (like grep)
		w.Header().Set("Content-Type", "text/plain")
		for _, result := range results {
			fmt.Fprintln(w, result)
		}
		return
	}

	// Regular checkpoint listing (reverse order by default)
	checkpoints, err := h.system.ListCheckpoints(ctx)
	if err != nil {
		h.logger.Error("Failed to list checkpoints", "error", err)
		http.Error(w, fmt.Sprintf("Failed to list checkpoints: %v", err), http.StatusInternalServerError)
		return
	}

	// Convert to response format
	type CheckpointResponse struct {
		ID         string    `json:"id"`
		CreateTime time.Time `json:"create_time"`
		SourceID   string    `json:"source_id,omitempty"`
	}

	var response []CheckpointResponse
	for _, cp := range checkpoints {
		response = append(response, CheckpointResponse{
			ID:         cp.ID,
			CreateTime: cp.CreateTime,
			SourceID:   cp.SourceID,
		})
	}

	w.Header().Set("Content-Type", "application/json")
	if err := json.NewEncoder(w).Encode(response); err != nil {
		h.logger.Error("Failed to encode response", "error", err)
	}
}

// HandleGetCheckpoint handles GET /sprites/{id}/checkpoints/{checkpoint_id}
// @public
// @operation GET /v1/sprites/{id}/checkpoints/{checkpoint_id}
// @summary Get sprite checkpoint details
// @description Retrieve detailed information about a specific checkpoint for a sprite
// @tags Sprites
// @security Bearer
// @param id path string true "Sprite ID"
// @param checkpoint_id path string true "Checkpoint ID"
// @response 200 {object} string "Checkpoint details"
// @response 401 {string} string "Unauthorized - invalid or missing authentication"
// @response 404 {string} string "Checkpoint not found"
// @response 500 {string} string "Internal server error"
// @response 503 {string} string "Service unavailable - JuiceFS not configured"
func (h *Handlers) HandleGetCheckpoint(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodGet {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	// Extract checkpoint ID from path
	// Expected format: /checkpoints/{id}
	parts := strings.Split(strings.Trim(r.URL.Path, "/"), "/")
	if len(parts) != 2 || parts[0] != "checkpoints" {
		http.NotFound(w, r)
		return
	}
	checkpointID := parts[1]

	// Storage readiness will be checked by the actual operations

	ctx := r.Context()
	checkpoint, err := h.system.GetCheckpoint(ctx, checkpointID)
	if err != nil {
		if strings.Contains(err.Error(), "does not exist") {
			http.NotFound(w, r)
			return
		}
		h.logger.Error("Failed to get checkpoint", "error", err, "checkpointID", checkpointID)
		http.Error(w, fmt.Sprintf("Failed to get checkpoint: %v", err), http.StatusInternalServerError)
		return
	}

	// Convert to response format
	response := struct {
		ID         string    `json:"id"`
		CreateTime time.Time `json:"create_time"`
		SourceID   string    `json:"source_id,omitempty"`
		History    []string  `json:"history,omitempty"`
	}{
		ID:         checkpoint.ID,
		CreateTime: checkpoint.CreateTime,
		SourceID:   checkpoint.SourceID,
		History:    checkpoint.History,
	}

	w.Header().Set("Content-Type", "application/json")
	if err := json.NewEncoder(w).Encode(response); err != nil {
		h.logger.Error("Failed to encode response", "error", err)
	}
}

// HandleCheckpointRestore handles POST /sprites/{id}/checkpoints/{checkpoint_id}/restore
// @public
// @operation POST /v1/sprites/{id}/checkpoints/{checkpoint_id}/restore
// @summary Restore sprite from checkpoint
// @description Restore a sprite from a specific checkpoint with real-time streaming progress
// @tags Sprites
// @security Bearer
// @param id path string true "Sprite ID"
// @param checkpoint_id path string true "Checkpoint ID to restore from"
// @response 200 {string} string "Streaming NDJSON with restore progress"
// @response 401 {string} string "Unauthorized - invalid or missing authentication"
// @response 404 {string} string "Checkpoint not found"
// @response 500 {string} string "Internal server error"
// @response 503 {string} string "Service unavailable - JuiceFS not configured"
func (h *Handlers) HandleCheckpointRestore(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	// Extract checkpoint ID from path
	// Expected format: /checkpoints/{id}/restore
	parts := strings.Split(strings.Trim(r.URL.Path, "/"), "/")
	if len(parts) != 3 || parts[0] != "checkpoints" || parts[2] != "restore" {
		http.NotFound(w, r)
		return
	}
	checkpointID := parts[1]

	h.logger.Info("Restore request", "checkpoint_id", checkpointID)

	// Storage readiness will be checked by the actual operations

	// Create channel for streaming messages
	streamCh := make(chan api.StreamMessage, 10)

	// Set up streaming response
	w.Header().Set("Content-Type", "application/x-ndjson")
	w.Header().Set("Cache-Control", "no-cache")
	w.Header().Set("X-Content-Type-Options", "nosniff")
	w.WriteHeader(http.StatusOK)

	// Ensure we can flush
	flusher, ok := w.(http.Flusher)
	if !ok {
		// Send error through channel before closing
		streamCh <- api.StreamMessage{
			Type:  "error",
			Error: "Streaming not supported",
			Time:  time.Now(),
		}
		close(streamCh)
		return
	}

	encoder := json.NewEncoder(w)

	// Start restore operation in background
	go func() {
		ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
		defer cancel()

		// Perform restore with streaming
		err := h.system.RestoreWithStream(ctx, checkpointID, streamCh)
		if err != nil {
			h.logger.Error("Restore failed", "error", err)
		}
	}()

	// Stream messages
	for msg := range streamCh {
		if err := encoder.Encode(msg); err != nil {
			h.logger.Error("Failed to encode message", "error", err)
			break
		}
		flusher.Flush()
	}
}

// HandleDeleteCheckpoint handles DELETE /checkpoints/{id}
func (h *Handlers) HandleDeleteCheckpoint(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodDelete {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	// Extract checkpoint ID from path
	parts := strings.Split(strings.Trim(r.URL.Path, "/"), "/")
	if len(parts) != 2 || parts[0] != "checkpoints" {
		http.NotFound(w, r)
		return
	}
	checkpointID := parts[1]

	if checkpointID == "active" || strings.EqualFold(checkpointID, "Current") {
		http.Error(w, "cannot delete active checkpoint", http.StatusConflict)
		return
	}

	ctx := r.Context()
	if err := h.system.DeleteCheckpoint(ctx, checkpointID); err != nil {
		if strings.Contains(err.Error(), "not found") {
			http.NotFound(w, r)
			return
		}
		if strings.Contains(err.Error(), "cannot delete active") {
			http.Error(w, err.Error(), http.StatusConflict)
			return
		}
		h.logger.Error("Failed to delete checkpoint", "error", err, "checkpointID", checkpointID)
		http.Error(w, fmt.Sprintf("Failed to delete checkpoint: %v", err), http.StatusInternalServerError)
		return
	}

	w.WriteHeader(http.StatusNoContent)
}

// HandleCheckpoint handles POST /sprites/{id}/checkpoint
// @public
// @operation POST /v1/sprites/{id}/checkpoint
// @summary Create sprite checkpoint
// @description Create a new checkpoint of the current sprite state with real-time streaming progress. Checkpoints are automatically versioned as v0, v1, v2, etc.
// @tags Sprites
// @security Bearer
// @param id path string true "Sprite ID"
// @response 200 {string} string "Streaming NDJSON with checkpoint progress"
// @response 401 {string} string "Unauthorized - invalid or missing authentication"
// @response 500 {string} string "Internal server error"
// @response 503 {string} string "Service unavailable - no process running or JuiceFS not configured"
func (h *Handlers) HandleCheckpoint(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	h.logger.Info("Checkpoint request")

	// Check if checkpoint process is supported
	if !h.system.IsProcessRunning() {
		http.Error(w, "No process is running to checkpoint", http.StatusServiceUnavailable)
		return
	}

	// Storage readiness will be checked by the actual operations

	// Create channel for streaming messages
	streamCh := make(chan api.StreamMessage, 10)

	// Set up streaming response
	w.Header().Set("Content-Type", "application/x-ndjson")
	w.Header().Set("Cache-Control", "no-cache")
	w.Header().Set("X-Content-Type-Options", "nosniff")
	w.WriteHeader(http.StatusOK)

	// Ensure we can flush
	flusher, ok := w.(http.Flusher)
	if !ok {
		http.Error(w, "Streaming not supported", http.StatusInternalServerError)
		return
	}

	encoder := json.NewEncoder(w)

	// Start checkpoint operation in background
	go func() {
		ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
		defer cancel()

		// Perform checkpoint with streaming (ID is ignored)
		err := h.system.CheckpointWithStream(ctx, "", streamCh)
		if err != nil {
			h.logger.Error("Checkpoint failed", "error", err)
		}
	}()

	// Stream messages
	for msg := range streamCh {
		if err := encoder.Encode(msg); err != nil {
			h.logger.Error("Failed to encode message", "error", err)
			break
		}
		flusher.Flush()
	}
}
