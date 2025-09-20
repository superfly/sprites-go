package commands

import (
	"log/slog"
	"net/url"
	"os"
	"strings"

	"github.com/superfly/sprite-env/client/config"
)

// getSpritesAPIURL returns the base URL for the Sprites API
// It checks SPRITE_URL first, then SPRITES_API_URL environment variable, then falls back to defaults
func getSpritesAPIURL(org *config.Organization) string {
	// Helper to extract base URL (scheme + host only)
	extractBaseURL := func(rawURL string) string {
		parsed, err := url.Parse(rawURL)
		if err != nil {
			// If parsing fails, return as-is but trimmed
			return strings.TrimRight(rawURL, "/")
		}
		// Return just scheme://host
		return parsed.Scheme + "://" + parsed.Host
	}

	// Use organization URL if available
	if org != nil && org.URL != "" {
		result := extractBaseURL(org.URL)
		slog.Default().Debug("Using org URL", "original", org.URL, "base", result)
		return result
	}

	// Fall back to environment variables if no org
	if apiURL := os.Getenv("SPRITE_URL"); apiURL != "" {
		result := extractBaseURL(apiURL)
		slog.Default().Debug("Using SPRITE_URL env var", "original", apiURL, "base", result)
		return result
	}
	if apiURL := os.Getenv("SPRITES_API_URL"); apiURL != "" {
		result := extractBaseURL(apiURL)
		slog.Default().Debug("Using SPRITES_API_URL env var", "original", apiURL, "base", result)
		return result
	}

	// Default to api.sprites.dev
	result := "https://api.sprites.dev"
	slog.Default().Debug("Using default URL", "url", result)
	return result
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
// This is the only function that should be used to create sprite proxy URLs
func buildSpriteProxyURL(org *config.Organization, spriteName string, path string) string {
	baseURL := getSpritesAPIURL(org)

	// For empty path, don't add any suffix
	if path == "" {
		return baseURL + "/v1/sprites/" + spriteName
	}

	// Clean up the path
	if !strings.HasPrefix(path, "/") {
		path = "/" + path
	}

	// Always use the pattern /v1/sprites/:name/<path>
	return baseURL + "/v1/sprites/" + spriteName + path
}
