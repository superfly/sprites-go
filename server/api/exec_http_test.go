package api

import (
	"io"
	"net/http"
	"net/http/httptest"
	"net/url"
	"strings"
	"testing"
)

func TestExecHTTP_NonTTY_Echo(t *testing.T) {
	h := &Handlers{logger: testLogger(t)}

	rr := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodPost, "/exec?cmd=echo&cmd=hello&dir=/", nil)
	h.ExecHTTPHandler(rr, req)

	resp := rr.Result()
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		t.Fatalf("expected 200, got %d", resp.StatusCode)
	}

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		t.Fatalf("read body: %v", err)
	}

	if len(body) < 3 {
		t.Fatalf("unexpected short body: %d", len(body))
	}

	// Expect final two bytes to be exit frame: 0x03 <code>
	if body[len(body)-2] != 0x03 || body[len(body)-1] != 0x00 {
		t.Fatalf("missing exit frame at end: %v", body[len(body)-2:])
	}

	// Ensure stdout payload contains "hello\n" preceded by 0x01 somewhere
	payload := string(body)
	if !strings.Contains(payload, string([]byte{0x01})+"hello\n") {
		t.Fatalf("stdout frame not found in payload: %q", payload)
	}
}

func TestExecHTTP_RejectTTY(t *testing.T) {
	h := &Handlers{logger: testLogger(t)}
	rr := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodPost, "/exec?cmd=echo&cmd=hi&tty=true", nil)
	h.ExecHTTPHandler(rr, req)
	if rr.Code != http.StatusBadRequest {
		t.Fatalf("expected 400, got %d", rr.Code)
	}
}

func TestExecHTTP_RejectTmuxParams(t *testing.T) {
	h := &Handlers{logger: testLogger(t)}
	rr := httptest.NewRecorder()
	q := url.Values{}
	q.Set("cmd", "echo")
	q.Add("cmd", "hi")
	q.Set("id", "sess")
	req := httptest.NewRequest(http.MethodPost, "/exec?"+q.Encode(), nil)
	h.ExecHTTPHandler(rr, req)
	if rr.Code != http.StatusBadRequest {
		t.Fatalf("expected 400, got %d", rr.Code)
	}
}
