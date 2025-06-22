package handlers

import (
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
	if !h.processManager.IsProcessRunning() {
		http.Error(w, "No process is running to checkpoint", http.StatusServiceUnavailable)
		return
	}

	// Create channel for streaming messages
	streamCh := make(chan api.StreamMessage, 10)

	// Send checkpoint command
	responseCh := make(chan CommandResponse)
	h.commandCh <- Command{
		Type:     CommandCheckpoint,
		Response: responseCh,
		Data: CheckpointData{
			CheckpointID: req.CheckpointID,
			StreamCh:     streamCh,
		},
	}

	// Check if command was accepted
	cmdResp := <-responseCh
	if !cmdResp.Success {
		http.Error(w, fmt.Sprintf("Failed to initiate checkpoint: %v", cmdResp.Error), http.StatusInternalServerError)
		return
	}

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

	// Check if process is already running
	if h.processManager.IsProcessRunning() {
		h.logger.Warn("Process is already running, cannot restore")
		http.Error(w, "Process is already running", http.StatusConflict)
		return
	}

	// Create channel for streaming messages
	streamCh := make(chan api.StreamMessage, 10)

	// Send restore command
	responseCh := make(chan CommandResponse)
	h.commandCh <- Command{
		Type:     CommandRestore,
		Response: responseCh,
		Data: RestoreData{
			CheckpointID: req.CheckpointID,
			StreamCh:     streamCh,
		},
	}

	// Check if command was accepted
	cmdResp := <-responseCh
	if !cmdResp.Success {
		h.logger.Error("Failed to initiate restore", "error", cmdResp.Error)
		// Send error message to stream
		streamCh <- api.StreamMessage{
			Type:  "error",
			Error: cmdResp.Error.Error(),
			Time:  time.Now(),
		}
		close(streamCh)
	}

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

	// Stream messages
	for msg := range streamCh {
		if err := encoder.Encode(msg); err != nil {
			h.logger.Error("Failed to encode message", "error", err)
			break
		}
		flusher.Flush()
	}
}
