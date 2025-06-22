package api

// CheckpointRequest represents the checkpoint API request
type CheckpointRequest struct {
	CheckpointID string `json:"checkpoint_id"`
}

// RestoreRequest represents the restore API request
type RestoreRequest struct {
	CheckpointID string `json:"checkpoint_id"`
}

// APIResponse represents a generic API response
// Used for simple responses that don't need streaming
type APIResponse struct {
	Status       string `json:"status,omitempty"`
	CheckpointID string `json:"checkpoint_id,omitempty"`
	Error        string `json:"error,omitempty"`
}
