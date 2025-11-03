package api

import (
	"bytes"
	"encoding/json"
	"testing"
	"time"
)

func TestSendCompletionEvent_ContainerPaths(t *testing.T) {
	// Arrange: create a buffer-backed encoder
	var buf bytes.Buffer
	enc := json.NewEncoder(&buf)

	// Act: send completion event
	sendCompletionEvent(enc, "demo", "/host/logs")

	// Decode the resulting JSON
	var ev ServiceLogEvent
	if err := json.Unmarshal(buf.Bytes(), &ev); err != nil {
		t.Fatalf("failed to unmarshal event: %v", err)
	}

	// Assert: type and log_files paths use container-mapped root
	if ev.Type != "complete" {
		t.Fatalf("expected type complete, got %s", ev.Type)
	}
	if ev.LogFiles == nil {
		t.Fatalf("expected log_files to be set")
	}
	wantStdout := "/.sprite/logs/services/demo.log"
	wantStderr := "/.sprite/logs/services/demo.stderr.log"
	if ev.LogFiles["stdout"] != wantStdout {
		t.Errorf("stdout path mismatch: want %q, got %q", wantStdout, ev.LogFiles["stdout"])
	}
	if ev.LogFiles["stderr"] != wantStderr {
		t.Errorf("stderr path mismatch: want %q, got %q", wantStderr, ev.LogFiles["stderr"])
	}

	// Ensure timestamp is reasonable (non-zero, recent)
	if ev.Timestamp <= 0 {
		t.Errorf("expected timestamp to be set")
	}
	// Optionally ensure it's within a recent window
	now := time.Now().UnixMilli()
	if ev.Timestamp > now || now-ev.Timestamp > 5000 {
		t.Errorf("timestamp out of expected range: now=%d, ts=%d", now, ev.Timestamp)
	}
}
