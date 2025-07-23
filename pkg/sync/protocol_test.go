package sync

import (
	"testing"
	"time"
)

func TestNewMessage(t *testing.T) {
	data := FileInfo{
		Path: "test.txt",
		Hash: "abc123",
		Size: 100,
	}

	msg, err := NewMessage(MsgTypeFileInfo, data)
	if err != nil {
		t.Fatalf("Failed to create message: %v", err)
	}

	if msg.Type != MsgTypeFileInfo {
		t.Errorf("Expected type %s, got %s", MsgTypeFileInfo, msg.Type)
	}

	if msg.Timestamp.IsZero() {
		t.Error("Expected timestamp to be set")
	}

	if msg.Data == nil {
		t.Error("Expected data to be set")
	}

	// Test unmarshaling
	var fileInfo FileInfo
	if err := msg.UnmarshalData(&fileInfo); err != nil {
		t.Fatalf("Failed to unmarshal data: %v", err)
	}

	if fileInfo.Path != data.Path {
		t.Errorf("Expected path %s, got %s", data.Path, fileInfo.Path)
	}

	if fileInfo.Hash != data.Hash {
		t.Errorf("Expected hash %s, got %s", data.Hash, fileInfo.Hash)
	}

	if fileInfo.Size != data.Size {
		t.Errorf("Expected size %d, got %d", data.Size, fileInfo.Size)
	}
}

func TestMessageTypes(t *testing.T) {
	tests := []struct {
		msgType MessageType
		data    interface{}
	}{
		{MsgTypeFileInfo, FileInfo{Path: "test.txt", Hash: "abc123", Size: 100}},
		{MsgTypeFileNeeded, FileNeeded{Path: "test.txt", ChannelID: 1}},
		{MsgTypeFileSkipped, FileSkipped{Path: "test.txt", Reason: "exists"}},
		{MsgTypeError, Error{Message: "test error"}},
		{MsgTypeProgress, Progress{FilesProcessed: 5, FilesTotal: 10}},
	}

	for _, test := range tests {
		msg, err := NewMessage(test.msgType, test.data)
		if err != nil {
			t.Errorf("Failed to create message for type %s: %v", test.msgType, err)
			continue
		}

		if msg.Type != test.msgType {
			t.Errorf("Expected type %s, got %s", test.msgType, msg.Type)
		}

		if time.Since(msg.Timestamp) > time.Second {
			t.Errorf("Message timestamp seems too old: %v", msg.Timestamp)
		}
	}
}

func TestNegotiationCompleteWithToken(t *testing.T) {
	data := NegotiationComplete{
		TotalFiles:   10,
		FilesNeeded:  5,
		FilesSkipped: 5,
		Channels:     4,
		SessionToken: "abc123def456",
	}

	msg, err := NewMessage(MsgTypeNegotiation, data)
	if err != nil {
		t.Fatalf("Failed to create message: %v", err)
	}

	var negComplete NegotiationComplete
	if err := msg.UnmarshalData(&negComplete); err != nil {
		t.Fatalf("Failed to unmarshal data: %v", err)
	}

	if negComplete.SessionToken != data.SessionToken {
		t.Errorf("Expected session token %s, got %s", data.SessionToken, negComplete.SessionToken)
	}

	if negComplete.Channels != data.Channels {
		t.Errorf("Expected channels %d, got %d", data.Channels, negComplete.Channels)
	}
}

func TestTransferAuth(t *testing.T) {
	data := TransferAuth{
		SessionToken: "abc123def456",
		ChannelID:    2,
	}

	msg, err := NewMessage(MsgTypeTransferAuth, data)
	if err != nil {
		t.Fatalf("Failed to create message: %v", err)
	}

	var transferAuth TransferAuth
	if err := msg.UnmarshalData(&transferAuth); err != nil {
		t.Fatalf("Failed to unmarshal data: %v", err)
	}

	if transferAuth.SessionToken != data.SessionToken {
		t.Errorf("Expected session token %s, got %s", data.SessionToken, transferAuth.SessionToken)
	}

	if transferAuth.ChannelID != data.ChannelID {
		t.Errorf("Expected channel ID %d, got %d", data.ChannelID, transferAuth.ChannelID)
	}
}
