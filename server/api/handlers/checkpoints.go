package handlers

import (
	"encoding/json"
	"fmt"
	"net/http"
	"time"
)

// HandleCheckpoint handles the /checkpoint endpoint
func (h *Handlers) HandleCheckpoint(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

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

	// Set up streaming response
	w.Header().Set("Content-Type", "application/x-ndjson")
	w.Header().Set("Cache-Control", "no-cache")
	w.Header().Set("Connection", "keep-alive")
	w.Header().Set("X-Content-Type-Options", "nosniff")
	w.WriteHeader(http.StatusOK)

	// Create encoder for JSON output
	encoder := json.NewEncoder(w)

	// Create streaming channel
	streamCh := make(chan StreamMessage, 10)
	done := make(chan struct{})

	// Stream messages to client
	go func() {
		defer close(done)
		for msg := range streamCh {
			if err := encoder.Encode(&msg); err != nil {
				h.logger.Error("Failed to encode checkpoint message", "error", err)
				return
			}
			if f, ok := w.(http.Flusher); ok {
				f.Flush()
			}
		}
	}()

	// Send checkpoint command with stream channel
	responseCh := make(chan CommandResponse)
	h.commandCh <- Command{
		Type:     CommandCheckpoint,
		Response: responseCh,
		Data: CheckpointData{
			CheckpointID: req.CheckpointID,
			StreamCh:     streamCh,
		},
	}

	// Wait for response
	resp := <-responseCh

	// Log the result but don't send to channel - streamingCheckpoint handles all messaging
	if resp.Success {
		h.logger.Info("Checkpoint created via API", "checkpointID", req.CheckpointID)
	} else {
		h.logger.Error("Failed to create checkpoint", "error", resp.Error, "checkpointID", req.CheckpointID)
	}

	// Wait for writer to finish - streamingCheckpoint will close the channel
	<-done
}

// HandleRestore handles the /restore endpoint
func (h *Handlers) HandleRestore(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

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

	// Set up streaming response
	w.Header().Set("Content-Type", "application/x-ndjson")
	w.Header().Set("Cache-Control", "no-cache")
	w.Header().Set("Connection", "keep-alive")
	w.Header().Set("X-Content-Type-Options", "nosniff")
	w.WriteHeader(http.StatusOK)

	// Create encoder for JSON output
	encoder := json.NewEncoder(w)

	// Create streaming channel
	streamCh := make(chan StreamMessage, 10)
	done := make(chan struct{})

	// Stream messages to client
	go func() {
		defer close(done)
		for msg := range streamCh {
			if err := encoder.Encode(&msg); err != nil {
				h.logger.Error("Failed to encode restore message", "error", err)
				return
			}
			if f, ok := w.(http.Flusher); ok {
				f.Flush()
			}
		}
	}()

	// Send initial message
	streamCh <- StreamMessage{
		Type: "info",
		Data: fmt.Sprintf("Starting restore from checkpoint %s", req.CheckpointID),
		Time: time.Now(),
	}

	// Send restore command with stream channel
	responseCh := make(chan CommandResponse)
	h.commandCh <- Command{
		Type:     CommandRestore,
		Response: responseCh,
		Data: RestoreData{
			CheckpointID: req.CheckpointID,
			StreamCh:     streamCh,
		},
	}

	// Wait for response (this confirms the restore was initiated)
	resp := <-responseCh
	if !resp.Success {
		streamCh <- StreamMessage{
			Type:  "error",
			Error: fmt.Sprintf("Failed to initiate restore: %v", resp.Error),
			Time:  time.Now(),
		}
		h.logger.Error("Failed to initiate restore", "error", resp.Error, "checkpointID", req.CheckpointID)
		close(streamCh)
		<-done
		return
	}

	h.logger.Info("Restore initiated via API", "checkpointID", req.CheckpointID)

	// Wait for streaming to complete
	// The restore process will close the channel when done
	<-done
}
