package sprites

import (
	"fmt"
	"io"
	"net/http"
	"regexp"
	"strings"
	"unicode"
)

// connectionError keeps the handshake cause and API metadata available to
// errors.Is/As, while rendering only bounded, sanitized diagnostics.
type connectionError struct {
	message string
	causes  []error
}

func (e *connectionError) Error() string   { return e.message }
func (e *connectionError) Unwrap() []error { return e.causes }

var (
	connectionCredentials = regexp.MustCompile(`(?i)(authorization|proxy-authorization|cookie|set-cookie|token|password|secret|api[_-]?key)\s*["']?\s*[:=]\s*[^\r\n,;]+|\b(bearer|basic)\s+[^\s"<>]+`)
	connectionURL         = regexp.MustCompile(`(?i)(https?|wss?)://[^\s"<>]+`)
)

func sanitizeConnectionDetail(s string, header http.Header) string {
	// Remove the actual credentials even when a server echoes only their value.
	for _, key := range []string{"Authorization", "Proxy-Authorization", "Cookie"} {
		for _, value := range header.Values(key) {
			if value != "" {
				s = strings.ReplaceAll(s, value, "[redacted]")
			}
			if key != "Cookie" {
				if _, secret, ok := strings.Cut(value, " "); ok && secret != "" {
					s = strings.ReplaceAll(s, secret, "[redacted]")
				}
			} else {
				for _, cookie := range strings.Split(value, ";") {
					if _, secret, ok := strings.Cut(cookie, "="); ok && strings.TrimSpace(secret) != "" {
						s = strings.ReplaceAll(s, strings.TrimSpace(secret), "[redacted]")
					}
				}
			}
		}
	}
	s = connectionCredentials.ReplaceAllString(s, "[redacted]")
	// URLs can contain credentials, query tokens, command arguments, or env vars.
	s = connectionURL.ReplaceAllString(s, "[redacted URL]")
	s = strings.Map(func(r rune) rune {
		if unicode.IsControl(r) {
			return ' '
		}

		return r
	}, s)
	s = strings.Join(strings.Fields(s), " ")
	if len(s) > 512 {
		s = s[:512] + "..."
	}

	return s
}

func commandConnectionError(operation string, cause error, resp *http.Response, header http.Header) error {
	e := &connectionError{message: operation, causes: []error{cause}}
	if resp != nil {
		e.message += fmt.Sprintf(" (HTTP %d)", resp.StatusCode)
		// Allowlist correlation headers; never dump request/response headers.
		for _, key := range []string{"Fly-Request-Id", "X-Request-Id", "X-Correlation-Id"} {
			if id := sanitizeConnectionDetail(resp.Header.Get(key), header); id != "" {
				if len(id) > 80 {
					id = id[:80]
				}
				e.message += "; " + strings.ToLower(key) + ": " + id
			}
		}
		var body []byte
		if resp.Body != nil {
			body, _ = io.ReadAll(io.LimitReader(resp.Body, 8192))
			resp.Body.Close()
		}
		if apiErr := parseAPIError(resp, body); apiErr != nil {
			apiErr.Message = sanitizeConnectionDetail(apiErr.Error(), header)
			apiErr.ErrorCode = sanitizeConnectionDetail(apiErr.ErrorCode, header)
			for i := range apiErr.Errors {
				apiErr.Errors[i] = sanitizeConnectionDetail(apiErr.Errors[i], header)
			}
			apiErr.RequestID = sanitizeConnectionDetail(apiErr.RequestID, header)
			apiErr.UpgradeURL = "" // Do not retain arbitrary response URLs in diagnostics.
			e.causes = append(e.causes, apiErr)
			e.message += ": " + apiErr.Message
		} else if detail := sanitizeConnectionDetail(string(body), header); detail != "" {
			e.message += ": " + detail
		}
	}
	e.message += ": " + sanitizeConnectionDetail(cause.Error(), header)

	return e
}
