package sprites

import (
	"encoding/json"
	"testing"
)

func TestStreamMessageDecodesErrorCode(t *testing.T) {
	var msg StreamMessage
	if err := json.Unmarshal([]byte(`{"type":"error","error":"outcome unknown","code":"operation_indeterminate"}`), &msg); err != nil {
		t.Fatal(err)
	}
	if msg.Code != StreamErrorCodeOperationIndeterminate {
		t.Fatalf("Code = %q, want %q", msg.Code, StreamErrorCodeOperationIndeterminate)
	}
}
