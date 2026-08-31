package sprites

import (
	"encoding/json"
	"errors"
	"fmt"
	"net/http"
	"strconv"
)

// Error codes returned by the API for rate limiting
const (
	ErrCodeCreationRateLimited     = "sprite_creation_rate_limited"
	ErrCodeConcurrentLimitExceeded = "concurrent_sprite_limit_exceeded"
)

// APIError represents a structured error response from the Sprites API.
// It implements the error interface and provides detailed information about
// rate limits and other API errors.
type APIError struct {
	// ErrorCode is the machine-readable error code (e.g., "sprite_creation_rate_limited")
	ErrorCode string `json:"error"`

	// Message is the human-readable error message
	Message string `json:"message"`

	// Limit is the rate limit value (e.g., 10 sprites per minute)
	Limit int `json:"limit,omitempty"`

	// WindowSeconds is the rate limit window in seconds
	WindowSeconds int `json:"window_seconds,omitempty"`

	// RetryAfterSeconds is the number of seconds to wait before retrying
	RetryAfterSeconds int `json:"retry_after_seconds,omitempty"`

	// CurrentCount is the current count (for concurrent limit errors)
	CurrentCount int `json:"current_count,omitempty"`

	// UpgradeAvailable indicates if an upgrade is available
	UpgradeAvailable bool `json:"upgrade_available,omitempty"`

	// UpgradeURL is the URL to upgrade the account (for rate limit errors)
	UpgradeURL string `json:"upgrade_url,omitempty"`

	// StatusCode is the HTTP status code (not from JSON, set by parser)
	StatusCode int `json:"-"`

	// RetryAfterHeader is the Retry-After header value in seconds
	RetryAfterHeader int `json:"-"`

	// RateLimitLimit is the X-RateLimit-Limit header value
	RateLimitLimit int `json:"-"`

	// RateLimitRemaining is the X-RateLimit-Remaining header value
	RateLimitRemaining int `json:"-"`

	// RateLimitReset is the X-RateLimit-Reset header value (Unix timestamp)
	RateLimitReset int64 `json:"-"`

	// RequestID is the Fly-Request-Id header, which correlates this call
	// with sprites-api and fly-proxy logs. Set from the response, never
	// from the body.
	RequestID string `json:"-"`
}

// Error implements the error interface
func (e *APIError) Error() string {
	if e.Message != "" {
		return e.Message
	}
	if e.ErrorCode != "" {
		return e.ErrorCode
	}

	return fmt.Sprintf("API error (status %d)", e.StatusCode)
}

// IsRateLimitError returns true if this is a 429 rate limit error
func (e *APIError) IsRateLimitError() bool {
	return e.StatusCode == http.StatusTooManyRequests
}

// IsCreationRateLimited returns true if this is a sprite creation rate limit error
func (e *APIError) IsCreationRateLimited() bool {
	return e.ErrorCode == ErrCodeCreationRateLimited
}

// IsConcurrentLimitExceeded returns true if this is a concurrent sprite limit error
func (e *APIError) IsConcurrentLimitExceeded() bool {
	return e.ErrorCode == ErrCodeConcurrentLimitExceeded
}

// GetRetryAfterSeconds returns the number of seconds to wait before retrying.
// It prefers the JSON field, falling back to the header value.
func (e *APIError) GetRetryAfterSeconds() int {
	if e.RetryAfterSeconds > 0 {
		return e.RetryAfterSeconds
	}

	return e.RetryAfterHeader
}

// parseAPIError attempts to parse a structured API error from an HTTP response.
// Returns nil if the response is not an error (status < 400).
func parseAPIError(resp *http.Response, body []byte) *APIError {
	if resp.StatusCode < 400 {
		return nil
	}

	apiErr := &APIError{
		StatusCode: resp.StatusCode,
	}

	// Correlation first: it is the field that stays useful when everything
	// else about the response is empty.
	apiErr.RequestID = resp.Header.Get("Fly-Request-Id")

	// Parse rate limit headers
	if ra := resp.Header.Get("Retry-After"); ra != "" {
		if v, err := strconv.Atoi(ra); err == nil {
			apiErr.RetryAfterHeader = v
		}
	}
	if rl := resp.Header.Get("X-RateLimit-Limit"); rl != "" {
		if v, err := strconv.Atoi(rl); err == nil {
			apiErr.RateLimitLimit = v
		}
	}
	if rr := resp.Header.Get("X-RateLimit-Remaining"); rr != "" {
		if v, err := strconv.Atoi(rr); err == nil {
			apiErr.RateLimitRemaining = v
		}
	}
	if rs := resp.Header.Get("X-RateLimit-Reset"); rs != "" {
		if v, err := strconv.ParseInt(rs, 10, 64); err == nil {
			apiErr.RateLimitReset = v
		}
	}

	// Try to parse JSON body
	if len(body) > 0 {
		// Attempt JSON parse - if it fails, just use raw body as message
		if err := json.Unmarshal(body, apiErr); err != nil {
			apiErr.Message = string(body)
		}
	}

	// Fallback message if nothing was parsed
	if apiErr.Message == "" && apiErr.ErrorCode == "" {
		apiErr.Message = fmt.Sprintf("API error (status %d)", resp.StatusCode)
	}

	return apiErr
}

// IsAPIError checks if an error is an APIError and returns it.
// Returns nil if the error is not an APIError.
func IsAPIError(err error) *APIError {
	if apiErr, ok := err.(*APIError); ok {
		return apiErr
	}

	return nil
}

// IsRateLimitError checks if an error is a rate limit error (HTTP 429).
// Returns the APIError if it is, nil otherwise.
func IsRateLimitErr(err error) *APIError {
	if apiErr := IsAPIError(err); apiErr != nil && apiErr.IsRateLimitError() {
		return apiErr
	}

	return nil
}

// ParseAPIError parses an API error from an HTTP response.
// Returns nil if the response is not an error (status < 400).
// This is the exported version of parseAPIError for use by clients.
func ParseAPIError(resp *http.Response, body []byte) *APIError {
	return parseAPIError(resp, body)
}

// StatusError renders a non-2xx response in the form callers have always
// seen, with the Fly request ID appended when the response carried one.
//
// Why the text is preserved rather than replaced by APIError.Error(): that
// method returns only the message, so routing these call sites through it
// would silently drop the "API returned status NNN" prefix that downstream
// tooling matches on. The point here is to ADD correlation, not to change
// what anything already parses.
//
// Why it matters: a non-2xx with an empty body renders as the whole of
//
//	API returned status 502:
//
// and there is nothing in that to find in a log. On one soak run a restore
// failed exactly that way, and a later search turned up a burst of 21
// fly-proxy PU02 502s it almost certainly belonged to -- "almost certainly"
// being where it stopped, because the request ID was sitting in the response
// this function's callers were discarding. See superfly/sprite-harness#92.
//
// Only Fly-Request-Id is added. Copying headers wholesale would eventually
// echo the Authorization header these requests set, into text that callers
// print and archive.
func StatusError(resp *http.Response, body []byte) error {
	msg := fmt.Sprintf("API returned status %d: %s", resp.StatusCode, string(body))
	if id := resp.Header.Get("Fly-Request-Id"); id != "" {
		msg += fmt.Sprintf("\nfly-request-id: %s", id)
	}

	return errors.New(msg)
}
