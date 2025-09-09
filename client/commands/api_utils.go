package commands

import (
	"log/slog"
	"net/url"
	"os"
	"strings"

	"github.com/superfly/sprite-env/client/config"
)

// getSpritesAPIURL returns the base URL for the Sprites API
// It checks SPRITES_API_URL environment variable first, then falls back to defaults
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

	if apiURL := os.Getenv("SPRITE_URL"); apiURL != "" {
		result := extractBaseURL(apiURL)
		slog.Default().Debug("Using SPRITE_URL env var", "original", apiURL, "base", result)
		return result
	}
	// Check for override via environment variable
	if apiURL := os.Getenv("SPRITES_API_URL"); apiURL != "" {
		result := extractBaseURL(apiURL)
		slog.Default().Debug("Using SPRITES_API_URL env var", "original", apiURL, "base", result)
		return result
	}

	// For organizations using api.sprites.dev, return that
	if org != nil && strings.Contains(org.URL, "api.sprites.dev") {
		result := extractBaseURL(org.URL)
		slog.Default().Debug("Using org URL", "original", org.URL, "base", result)
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

	// Clean up the path
	if !strings.HasPrefix(path, "/") {
		path = "/" + path
	}

	// Always use the pattern /v1/sprites/:name/<path>
	return baseURL + "/v1/sprites/" + spriteName + path
}
