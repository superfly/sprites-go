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
	// Statistics fields (optional, filled when stats are available)
	FileCount  int    `json:"file_count,omitempty"`
	DirCount   int    `json:"dir_count,omitempty"`
	TotalSize  int64  `json:"total_size,omitempty"`
	// Divergence info (only for active state)
	DivergenceIndicator string `json:"divergence,omitempty"`
	FilesDiff           int    `json:"files_diff,omitempty"`
	SizeDiff            int64  `json:"size_diff,omitempty"`
}

// APIResponse represents a generic API response
// Used for simple responses that don't need streaming
type APIResponse struct {
	Status       string `json:"status,omitempty"`
	CheckpointID string `json:"checkpoint_id,omitempty"`
	Error        string `json:"error,omitempty"`
}
