package sync

import (
	"encoding/json"
	"time"
)

// MessageType represents the type of WebSocket message
type MessageType string

const (
	// Negotiation phase messages
	MsgTypeFileInfo    MessageType = "file_info"
	MsgTypeFileNeeded  MessageType = "file_needed"
	MsgTypeFileSkipped MessageType = "file_skipped"
	MsgTypeNegotiation MessageType = "negotiation_complete"

	// Transfer connection messages
	MsgTypeTransferAuth  MessageType = "transfer_auth"
	MsgTypeTransferReady MessageType = "transfer_ready"

	// Upload phase messages
	MsgTypeUploadStart   MessageType = "upload_start"
	MsgTypeFileData      MessageType = "file_data"
	MsgTypeUploadDone    MessageType = "upload_done"
	MsgTypeUploadSuccess MessageType = "upload_success"
	MsgTypeUploadError   MessageType = "upload_error"

	// Progress and status messages
	MsgTypeProgress MessageType = "progress"
	MsgTypeError    MessageType = "error"
	MsgTypeComplete MessageType = "complete"
)

// Message represents a WebSocket message in the sync protocol
type Message struct {
	Type      MessageType     `json:"type"`
	Timestamp time.Time       `json:"timestamp"`
	Data      json.RawMessage `json:"data,omitempty"`
}

// FileInfo represents file metadata for negotiation
type FileInfo struct {
	Path string `json:"path"`
	Hash string `json:"hash"`
	Size int64  `json:"size"`
}

// FileNeeded indicates a file is needed for upload
type FileNeeded struct {
	Path      string `json:"path"`
	ChannelID int    `json:"channel_id"`
}

// FileSkipped indicates a file should be skipped
type FileSkipped struct {
	Path   string `json:"path"`
	Reason string `json:"reason,omitempty"`
}

// NegotiationComplete indicates negotiation phase is done
type NegotiationComplete struct {
	TotalFiles   int    `json:"total_files"`
	FilesNeeded  int    `json:"files_needed"`
	FilesSkipped int    `json:"files_skipped"`
	Channels     int    `json:"channels"`
	SessionToken string `json:"session_token"` // Cryptographic token for transfer connections
}

// UploadStart indicates start of file upload on a channel
type UploadStart struct {
	ChannelID int    `json:"channel_id"`
	Path      string `json:"path"`
	Hash      string `json:"hash"`
	Size      int64  `json:"size"`
}

// FileData contains file content chunk
type FileData struct {
	ChannelID int    `json:"channel_id"`
	Path      string `json:"path"`
	Data      []byte `json:"data"`
	Offset    int64  `json:"offset"`
	Final     bool   `json:"final"`
}

// UploadDone indicates successful file upload completion
type UploadDone struct {
	ChannelID int    `json:"channel_id"`
	Path      string `json:"path"`
	Hash      string `json:"hash"`
	Size      int64  `json:"size"`
}

// UploadSuccess indicates successful file upload
type UploadSuccess struct {
	ChannelID int    `json:"channel_id"`
	Path      string `json:"path"`
}

// UploadError indicates file upload error
type UploadError struct {
	ChannelID int    `json:"channel_id"`
	Path      string `json:"path"`
	Error     string `json:"error"`
}

// Progress represents sync progress
type Progress struct {
	FilesProcessed int   `json:"files_processed"`
	FilesTotal     int   `json:"files_total"`
	BytesUploaded  int64 `json:"bytes_uploaded"`
	BytesTotal     int64 `json:"bytes_total"`
}

// Error represents an error message
type Error struct {
	Message string `json:"message"`
	Code    string `json:"code,omitempty"`
}

// Complete represents successful sync completion
type Complete struct {
	FilesUploaded int           `json:"files_uploaded"`
	FilesSkipped  int           `json:"files_skipped"`
	BytesUploaded int64         `json:"bytes_uploaded"`
	Duration      time.Duration `json:"duration"`
}

// TransferAuth represents authentication for transfer connections
type TransferAuth struct {
	SessionToken string `json:"session_token"`
	ChannelID    int    `json:"channel_id"`
}

// TransferReady indicates transfer connection is ready
type TransferReady struct {
	ChannelID int `json:"channel_id"`
}

// NewMessage creates a new message with timestamp
func NewMessage(msgType MessageType, data interface{}) (*Message, error) {
	var rawData json.RawMessage
	if data != nil {
		bytes, err := json.Marshal(data)
		if err != nil {
			return nil, err
		}
		rawData = bytes
	}

	return &Message{
		Type:      msgType,
		Timestamp: time.Now(),
		Data:      rawData,
	}, nil
}

// UnmarshalData unmarshals the message data into the provided interface
func (m *Message) UnmarshalData(v interface{}) error {
	if m.Data == nil {
		return nil
	}
	return json.Unmarshal(m.Data, v)
}
