package handlers

import (
	"context"
	"encoding/json"
	"fmt"
	"lib/api"
	"net/http"
	"time"
)

// HandleCheckpoint handles POST /checkpoint
func (h *Handlers) HandleCheckpoint(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	// Parse request body
	var req struct {
		CheckpointID string `json:"checkpoint_id"`
	}
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, fmt.Sprintf("Invalid request body: %v", err), http.StatusBadRequest)
		return
	}

	if req.CheckpointID == "" {
		http.Error(w, "checkpoint_id is required", http.StatusBadRequest)
		return
	}

	h.logger.Info("Checkpoint request", "checkpoint_id", req.CheckpointID)

	// Check if checkpoint process is supported
	if !h.system.IsProcessRunning() {
		http.Error(w, "No process is running to checkpoint", http.StatusServiceUnavailable)
		return
	}

	// Check if JuiceFS is configured
	if !h.system.HasJuiceFS() {
		http.Error(w, "JuiceFS not configured", http.StatusServiceUnavailable)
		return
	}

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

		// Perform checkpoint with streaming
		err := h.system.CheckpointWithStream(ctx, req.CheckpointID, streamCh)
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

// HandleRestore handles POST /restore
func (h *Handlers) HandleRestore(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	// Parse request body
	var req struct {
		CheckpointID string `json:"checkpoint_id"`
	}
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, fmt.Sprintf("Invalid request body: %v", err), http.StatusBadRequest)
		return
	}

	if req.CheckpointID == "" {
		http.Error(w, "checkpoint_id is required", http.StatusBadRequest)
		return
	}

	h.logger.Info("Restore request", "checkpoint_id", req.CheckpointID)

	// Check if JuiceFS is configured
	if !h.system.HasJuiceFS() {
		http.Error(w, "JuiceFS not configured", http.StatusServiceUnavailable)
		return
	}

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
		err := h.system.RestoreWithStream(ctx, req.CheckpointID, streamCh)
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
