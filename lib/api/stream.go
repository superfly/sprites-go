package api

import "time"

// StreamMessage represents a streaming message (used for checkpoint/restore and other streaming endpoints)
type StreamMessage struct {
	Type  string    `json:"type"` // "info", "stdout", "stderr", "error", "complete"
	Data  string    `json:"data,omitempty"`
	Error string    `json:"error,omitempty"`
	Time  time.Time `json:"time"`
}
