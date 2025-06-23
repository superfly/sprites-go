package api

import "time"

// CheckpointRequest represents the checkpoint API request
type CheckpointRequest struct {
	CheckpointID string `json:"checkpoint_id"`
}

// RestoreRequest represents the restore API request
type RestoreRequest struct {
	CheckpointID string `json:"checkpoint_id"`
}

// CheckpointInfo contains information about a checkpoint
type CheckpointInfo struct {
	ID         string    `json:"id"`
	CreateTime time.Time `json:"create_time"`
	SourceID   string    `json:"source_id,omitempty"`
	History    []string  `json:"history,omitempty"`
}

// APIResponse represents a generic API response
// Used for simple responses that don't need streaming
type APIResponse struct {
	Status       string `json:"status,omitempty"`
	CheckpointID string `json:"checkpoint_id,omitempty"`
	Error        string `json:"error,omitempty"`
}
