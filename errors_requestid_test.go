package sprites

import (
	"net/http"
	"strings"
	"testing"
)

// hdr builds a response header set.
//
// Returns the header rather than a *http.Response on purpose: bodyclose
// treats any function returning *http.Response as an HTTP call whose body
// must be closed, which these header-only fixtures never have. Constructing
// the response inline at each site keeps the linter satisfied without a
// suppression comment.
func hdr(kv map[string]string) http.Header {
	h := http.Header{}
	for k, v := range kv {
		h.Set(k, v)
	}

	return h
}

// The motivating case: a non-2xx whose body is empty, so the status line is
// the entire error. Without the request ID there is nothing to search for.
func TestStatusErrorAppendsTheRequestIDOnAnEmptyBody(t *testing.T) {
	resp := &http.Response{StatusCode: 502, Header: hdr(map[string]string{"Fly-Request-Id": "01M19T3EMF8NHCPCPR0YN9ZRYW-lax"})}
	err := StatusError(resp, nil)
	if err == nil {
		t.Fatal("no error returned")
	}
	got := err.Error()
	if !strings.Contains(got, "API returned status 502") {
		t.Errorf("the established prefix was lost; downstream tooling matches on it: %q", got)
	}
	if !strings.Contains(got, "fly-request-id: 01M19T3EMF8NHCPCPR0YN9ZRYW-lax") {
		t.Errorf("request id not surfaced: %q", got)
	}
}

// The text callers have always seen must not change shape when there is no
// request ID to add.
func TestStatusErrorIsUnchangedWithoutAHeader(t *testing.T) {
	err := StatusError(&http.Response{StatusCode: 404, Header: hdr(nil)}, []byte("not found"))
	if got, want := err.Error(), "API returned status 404: not found"; got != want {
		t.Errorf("StatusError = %q, want %q", got, want)
	}
}

// These requests set an Authorization header, and the result of this
// function is printed by CLIs and archived by test harnesses. Only the one
// named header may be copied.
func TestStatusErrorNeverEchoesCredentials(t *testing.T) {
	resp := &http.Response{StatusCode: 401, Header: hdr(map[string]string{
		"Authorization":    "Bearer super-secret-token",
		"Set-Cookie":       "session=abc123",
		"WWW-Authenticate": `Bearer realm="sprites"`,
		"X-Api-Key":        "another-secret",
		"Fly-Request-Id":   "01M19T3EMF8NHCPCPR0YN9ZRYW-lax",
	})}
	got := StatusError(resp, []byte("unauthorized")).Error()
	for _, secret := range []string{"super-secret-token", "abc123", "another-secret", "realm"} {
		if strings.Contains(got, secret) {
			t.Errorf("a credential was echoed into the error text: %q", got)
		}
	}
	if !strings.Contains(got, "01M19T3EMF8NHCPCPR0YN9ZRYW-lax") {
		t.Error("the request id was dropped along with the credentials")
	}
}

// The structured path gets it too, so a caller inspecting *APIError does not
// have to scrape the string.
func TestParseAPIErrorCapturesTheRequestID(t *testing.T) {
	resp := &http.Response{StatusCode: 429, Header: hdr(map[string]string{
		"Fly-Request-Id": "01M19T3EMF8NHCPCPR0YN9ZRYW-ord",
		"Retry-After":    "30",
	})}
	apiErr := parseAPIError(resp, []byte(`{"error":"sprite_creation_rate_limited","message":"slow down"}`))
	if apiErr == nil {
		t.Fatal("no APIError parsed")
	}
	if apiErr.RequestID != "01M19T3EMF8NHCPCPR0YN9ZRYW-ord" {
		t.Errorf("RequestID = %q", apiErr.RequestID)
	}
	// And the existing behaviour is untouched.
	if !apiErr.IsRateLimitError() || apiErr.GetRetryAfterSeconds() != 30 {
		t.Errorf("existing APIError parsing regressed: %+v", apiErr)
	}
}

// A 2xx is not an error, and must not acquire one.
func TestParseAPIErrorStillIgnoresSuccess(t *testing.T) {
	if got := parseAPIError(&http.Response{StatusCode: 200, Header: hdr(map[string]string{"Fly-Request-Id": "x"})}, nil); got != nil {
		t.Errorf("parseAPIError on a 200 returned %+v, want nil", got)
	}
}
