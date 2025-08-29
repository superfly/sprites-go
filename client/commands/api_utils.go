package commands

import (
	"os"
	"strings"

	"github.com/superfly/sprite-env/client/config"
)

// getSpritesAPIURL returns the base URL for the Sprites API
// It checks SPRITES_API_URL environment variable first, then falls back to defaults
func getSpritesAPIURL(org *config.Organization) string {
	// Check for override via environment variable
	if apiURL := os.Getenv("SPRITES_API_URL"); apiURL != "" {
		return strings.TrimRight(apiURL, "/")
	}

	// For organizations using api.sprites.dev, return that
	if org != nil && strings.Contains(org.URL, "api.sprites.dev") {
		return strings.TrimRight(org.URL, "/")
	}

	// Default to api.sprites.dev
	return "https://api.sprites.dev"
}

// truncateToken returns a truncated version of a token for safe logging
// e.g. "abcdefghijklmnop" becomes "abc..nop"
func truncateToken(token string) string {
	if len(token) == 0 {
		return "<blank>"
	}
	if len(token) < 10 {
		// Very short token, just show partial
		if len(token) <= 3 {
			return token[:1] + "..."
		}
		return token[:3] + "..."
	}
	// Show first 3 and last 3 characters
	return token[:3] + ".." + token[len(token)-3:]
}

// buildSpriteProxyURL builds the URL for sprite proxy endpoints
func buildSpriteProxyURL(org *config.Organization, spriteName string, path string) string {
	baseURL := getSpritesAPIURL(org)

	// Clean up the path
	if !strings.HasPrefix(path, "/") {
		path = "/" + path
	}

	return baseURL + "/v1/sprites/" + spriteName + path
}
