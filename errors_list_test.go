package sprites

import (
	"net/http"
	"testing"
)

// errorFromBody builds an APIError the way a real response would.
func errorFromBody(t *testing.T, status int, body string) *APIError {
	t.Helper()

	resp := &http.Response{StatusCode: status, Header: http.Header{}}

	apiErr := parseAPIError(resp, []byte(body))
	if apiErr == nil {
		t.Fatalf("parseAPIError returned nil for status %d", status)
	}

	return apiErr
}

func TestAPIErrorReadsErrorList(t *testing.T) {
	// Validation failures are reported as a list, and until this was parsed
	// the reason was dropped and callers saw only the status.
	apiErr := errorFromBody(t, http.StatusBadRequest,
		`{"errors":["invalid runtime: nope, must be \"default\" or \"dev\""]}`)

	if got, want := apiErr.Error(), `invalid runtime: nope, must be "default" or "dev"`; got != want {
		t.Errorf("Error() = %q, want %q", got, want)
	}

	if len(apiErr.Errors) != 1 {
		t.Errorf("Errors = %v, want one entry", apiErr.Errors)
	}
}

func TestAPIErrorJoinsSeveralErrors(t *testing.T) {
	apiErr := errorFromBody(t, http.StatusBadRequest,
		`{"errors":["name is required","invalid region"]}`)

	if got, want := apiErr.Error(), "name is required; invalid region"; got != want {
		t.Errorf("Error() = %q, want %q", got, want)
	}
}

func TestAPIErrorPrefersMessageOverList(t *testing.T) {
	// A body carrying both should read as the singular message; the list is
	// still exposed for a caller that wants every reason.
	apiErr := errorFromBody(t, http.StatusBadRequest,
		`{"message":"the headline","errors":["a detail"]}`)

	if got, want := apiErr.Error(), "the headline"; got != want {
		t.Errorf("Error() = %q, want %q", got, want)
	}
	if len(apiErr.Errors) != 1 || apiErr.Errors[0] != "a detail" {
		t.Errorf("Errors = %v, want [a detail]", apiErr.Errors)
	}
}

func TestAPIErrorKeepsSingularShapes(t *testing.T) {
	// The shapes that already worked must keep working.
	if got := errorFromBody(t, http.StatusBadRequest, `{"error":"name is required"}`).Error(); got != "name is required" {
		t.Errorf("Error() = %q, want %q", got, "name is required")
	}

	if got := errorFromBody(t, http.StatusTooManyRequests,
		`{"error":"sprite_creation_rate_limited","message":"slow down"}`).Error(); got != "slow down" {
		t.Errorf("Error() = %q, want %q", got, "slow down")
	}
}

func TestAPIErrorFallsBackWithoutAnyMessage(t *testing.T) {
	if got, want := errorFromBody(t, http.StatusInternalServerError, `{}`).Error(),
		"API error (status 500)"; got != want {
		t.Errorf("Error() = %q, want %q", got, want)
	}

	// An empty list is not a message either.
	if got, want := errorFromBody(t, http.StatusInternalServerError, `{"errors":[]}`).Error(),
		"API error (status 500)"; got != want {
		t.Errorf("Error() = %q, want %q", got, want)
	}
}
