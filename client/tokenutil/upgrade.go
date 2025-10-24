package tokenutil

import (
	"context"
	"fmt"
	"log/slog"
	"os"
	"strings"
	"time"

	"github.com/superfly/sprite-env/client/keyring"
	sprites "github.com/superfly/sprites-go"
)

// IsLegacyToken checks if a token is in the legacy 3-part format
// Legacy format: org_slug/token_id/token_value
// New format: org_slug/fly_org_id/token_id/token_value
func IsLegacyToken(token string) bool {
	if token == "" {
		return false
	}

	parts := strings.Split(token, "/")
	return len(parts) == 3
}

// OrgInfo contains the minimal org information needed for token upgrade
type OrgInfo struct {
	Name       string
	URL        string
	KeyringKey string
}

// UserInfo contains the minimal user information needed for token upgrade
type UserInfo struct {
	ID string
}

// FlyTokenReader is a function type for reading Fly tokens
type FlyTokenReader func(userID string) (string, error)

// UpgradeTokenIfNeeded checks if a token is legacy and upgrades it automatically
// Returns the token (upgraded if needed) and whether an upgrade occurred
func UpgradeTokenIfNeeded(token string, org OrgInfo, user *UserInfo, flyTokenReader FlyTokenReader, keyringService string) (string, bool, error) {
	// Check if it's a legacy token
	if !IsLegacyToken(token) {
		slog.Debug("token is already in new format", "org", org.Name)
		return token, false, nil
	}

	slog.Info("detected legacy token format, upgrading to new format", "org", org.Name)

	// Show user-friendly message
	if isInteractive() {
		fmt.Fprintf(os.Stderr, "\n")
		fmt.Fprintf(os.Stderr, "📦 Upgrading to new token format for organization %s...\n", org.Name)
		fmt.Fprintf(os.Stderr, "   (This only needs to happen once)\n")
	}

	// Check we have user info
	if user == nil {
		return "", false, fmt.Errorf("no active user found - please run 'sprite login' to re-authenticate")
	}

	// Get Fly token for this user
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	flyToken, err := flyTokenReader(user.ID)
	if err != nil {
		return "", false, fmt.Errorf("failed to get Fly token for upgrade - please run 'sprite login' to re-authenticate: %w", err)
	}

	// Create a new Sprite token using the Fly token
	apiURL := org.URL
	if apiURL == "" {
		apiURL = "https://api.sprites.dev"
	}

	slog.Debug("requesting new token from sprites API",
		"org", org.Name,
		"apiURL", apiURL,
		"userID", user.ID)

	newToken, err := sprites.CreateToken(ctx, flyToken, org.Name, "", apiURL)
	if err != nil {
		return "", false, fmt.Errorf("failed to create new token: %w", err)
	}

	// Verify the new token is in the correct format
	if IsLegacyToken(newToken) {
		return "", false, fmt.Errorf("server returned a token in legacy format - please ensure the sprites API is updated")
	}

	slog.Debug("successfully obtained new token", "org", org.Name, "tokenParts", len(strings.Split(newToken, "/")))

	// Save the new token to keyring
	if org.KeyringKey != "" && keyringService != "" {
		if err := keyring.Set(keyringService, org.KeyringKey, newToken); err != nil {
			return "", false, fmt.Errorf("failed to save upgraded token to keyring: %w", err)
		}
		slog.Debug("saved upgraded token to keyring",
			"service", keyringService,
			"key", org.KeyringKey)
	}

	if isInteractive() {
		fmt.Fprintf(os.Stderr, "✓ Token upgraded successfully\n\n")
	}

	return newToken, true, nil
}

// isInteractive checks if we're running in an interactive terminal
func isInteractive() bool {
	fileInfo, err := os.Stderr.Stat()
	if err != nil {
		return false
	}
	return (fileInfo.Mode() & os.ModeCharDevice) != 0
}
