package sprites

import (
	"net/http"
	"regexp"
	"strings"
	"sync/atomic"

	"github.com/Masterminds/semver/v3"
)

// Minimum RC version that supports path-based attach endpoint
var attachPathMinRC = semver.MustParse("0.0.1-rc30")

// extractChannel returns the release channel from a version string.
// Returns "dev", "rc", or "release".
func extractChannel(version string) string {
	version = strings.TrimPrefix(version, "v")

	// Handle X.Y.Z-dev-<sha> format
	if strings.Contains(version, "-dev-") || strings.HasSuffix(version, "-dev") {
		return "dev"
	}

	// Match pattern like -rc1, -dev1, etc.
	re := regexp.MustCompile(`-([a-zA-Z]+)\d*$`)
	matches := re.FindStringSubmatch(version)

	if len(matches) > 1 {
		suffix := matches[1]
		if strings.HasPrefix(suffix, "dev") {
			return "dev"
		}
		if strings.HasPrefix(suffix, "rc") {
			return "rc"
		}
		return suffix
	}

	return "release"
}

// supportsPathAttach returns true if the server version supports
// the path-based attach endpoint (/exec/:id).
// Returns false for unknown versions or versions <= rc29.
func supportsPathAttach(version string) bool {
	if version == "" {
		return false
	}

	channel := extractChannel(version)

	// Dev versions always support path attach
	if channel == "dev" {
		return true
	}

	// Parse version for comparison
	v, err := semver.NewVersion(strings.TrimPrefix(version, "v"))
	if err != nil {
		return false // Cannot parse, use safe default
	}

	// RC versions: support path attach if >= rc30
	if channel == "rc" {
		return v.GreaterThan(attachPathMinRC) || v.Equal(attachPathMinRC)
	}

	// Release versions: support path attach
	return true
}

// versionCapturingTransport wraps an http.RoundTripper to capture Sprite-Version headers.
type versionCapturingTransport struct {
	wrapped   http.RoundTripper
	versionHolder *atomic.Value
}

func (t *versionCapturingTransport) RoundTrip(req *http.Request) (*http.Response, error) {
	resp, err := t.wrapped.RoundTrip(req)
	if err != nil {
		return resp, err
	}

	if version := resp.Header.Get("Sprite-Version"); version != "" {
		t.versionHolder.Store(version)
	}

	return resp, err
}
