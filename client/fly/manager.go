package fly

import (
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"os/exec"
	"runtime"
	"sort"
	"strings"
	"time"

	"github.com/superfly/sprite-env/client/config"
	"github.com/superfly/sprite-env/client/keyring"
)

const (
	// KeyringServicePrefix is the prefix for user-scoped keyring services
	KeyringServicePrefix = "sprites-cli-fly"
)

// Organization represents a Fly.io organization
type Organization struct {
	ID     string `json:"id"`
	Slug   string `json:"slug"`
	Name   string `json:"name"`
	Type   string `json:"type"`
	Status string `json:"status"`
}

// TokenInfo represents token information from the Fly API
type TokenInfo struct {
	Organization string `json:"organization"`
	OrgSlug      string `json:"org_slug"`
	TokenID      string `json:"token_id"`
	User         string `json:"user"`
}

// TokensResponse represents the response from the tokens API
type TokensResponse struct {
	Tokens []TokenInfo `json:"tokens"`
}

// Manager handles Fly.io authentication
type Manager struct {
	configMgr *config.Manager
}

// NewManager creates a new Fly.io auth manager
func NewManager(configMgr *config.Manager) *Manager {
	return &Manager{
		configMgr: configMgr,
	}
}

// GetOrCreateMacaroon gets a macaroon token for the given org
// It follows this priority:
// 1. Check if we have a macaroon in our keychain already
// 2. Check ~/.fly/ for a token
// 3. If token is not a macaroon, exchange it
// 4. If no token, run login flow
func (m *Manager) GetOrCreateMacaroon(ctx context.Context, orgSlug string) (string, error) {
	// Check for existing Fly token first to get user info
	flyToken, source, err := ReadFlyToken()
	if err != nil {
		if err == ErrNoToken {
			// No token found, need to login
			return m.runLoginFlow(ctx, orgSlug)
		}
		return "", fmt.Errorf("failed to read fly token: %w", err)
	}

	// Get current user to scope the keychain
	user, err := GetCurrentUser(ctx, flyToken)
	if err != nil {
		return "", fmt.Errorf("failed to get current user: %w", err)
	}

	return m.GetOrCreateMacaroonWithUser(ctx, orgSlug, flyToken, source, user)
}

// GetOrCreateMacaroonWithUser gets or creates a macaroon with user info already fetched
func (m *Manager) GetOrCreateMacaroonWithUser(ctx context.Context, orgSlug string, flyToken string, source string, user *User) (string, error) {
	// Build user-scoped service and key (using user ID, not email)
	keychainService := buildUserKeychainService(user.ID)
	keychainKey := buildFlyKeychainKey(orgSlug)

	// Check if we already have a macaroon stored for this user
	token, err := keyring.Get(keychainService, keychainKey)
	if err == nil && token != "" && IsMacaroon(token) {
		return token, nil
	}

	// We have a token, check if it's a macaroon
	if IsMacaroon(flyToken) {
		// Store it in our keychain
		if err := keyring.Set(keychainService, keychainKey, flyToken); err != nil {
			fmt.Printf("Warning: failed to store token in keychain: %v\n", err)
		}
		return flyToken, nil
	}

	// Token is not a macaroon, need to exchange it
	fmt.Printf("Exchanging Fly token for macaroon...\n")
	macaroon, err := ExchangeForMacaroon(ctx, flyToken, orgSlug)
	if err != nil {
		return "", fmt.Errorf("failed to exchange token for macaroon: %w", err)
	}

	// Store the macaroon in user-scoped keychain
	if err := keyring.Set(keychainService, keychainKey, macaroon); err != nil {
		fmt.Printf("Warning: failed to store macaroon in keychain: %v\n", err)
	}

	return macaroon, nil
}

// runLoginFlow runs the web-based login flow
func (m *Manager) runLoginFlow(ctx context.Context, orgSlug string) (string, error) {
	fmt.Println("No Fly.io token found. Starting web-based login...")

	// Get hostname for session
	hostname, err := getHostname()
	if err != nil {
		hostname = "sprite-cli"
	}

	// Start CLI session
	session, err := StartCLISession(hostname, map[string]interface{}{
		"signup": false,
		"target": "auth",
	})
	if err != nil {
		return "", fmt.Errorf("failed to start login session: %w", err)
	}

	// Open browser
	fmt.Printf("\nOpening %s in your browser...\n\n", session.URL)
	if err := openBrowser(session.URL); err != nil {
		fmt.Printf("Failed to open browser automatically. Please visit this URL:\n%s\n\n", session.URL)
	}

	// Wait for authentication
	fmt.Println("Waiting for authentication...")
	token, err := WaitForCLISession(ctx, session.ID)
	if err != nil {
		return "", fmt.Errorf("authentication failed: %w", err)
	}

	// Get user info from the token
	user, err := GetCurrentUser(ctx, token)
	if err != nil {
		return "", fmt.Errorf("failed to get user info: %w", err)
	}

	fmt.Printf("Authenticated as: %s\n", user.Email)

	// Exchange for macaroon
	fmt.Printf("Exchanging token for organization %s...\n", orgSlug)
	macaroon, err := ExchangeForMacaroon(ctx, token, orgSlug)
	if err != nil {
		return "", fmt.Errorf("failed to exchange token: %w", err)
	}

	// Store in user-scoped keychain (using user ID, not email)
	keychainService := buildUserKeychainService(user.ID)
	keychainKey := buildFlyKeychainKey(orgSlug)
	if err := keyring.Set(keychainService, keychainKey, macaroon); err != nil {
		fmt.Printf("Warning: failed to store macaroon in keychain: %v\n", err)
	}

	fmt.Println("Successfully authenticated with Fly.io")
	return macaroon, nil
}

// FetchOrganizations fetches the list of organizations accessible with the given token
func (m *Manager) FetchOrganizations(ctx context.Context, token string) ([]Organization, error) {
	url := "https://api.machines.dev/v1/tokens/current"

	req, err := http.NewRequestWithContext(ctx, http.MethodGet, url, nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	req.Header.Set("Authorization", AuthorizationHeader(token))

	client := &http.Client{Timeout: 30 * time.Second}
	resp, err := client.Do(req)
	if err != nil {
		return nil, fmt.Errorf("failed to fetch organizations: %w", err)
	}
	defer resp.Body.Close()

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, fmt.Errorf("failed to read response: %w", err)
	}

	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("API returned status %d: %s", resp.StatusCode, string(body))
	}

	var tokensResp TokensResponse
	if err := json.Unmarshal(body, &tokensResp); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	// Deduplicate organizations
	orgMap := make(map[string]*Organization)
	for _, token := range tokensResp.Tokens {
		if _, exists := orgMap[token.OrgSlug]; !exists {
			orgMap[token.OrgSlug] = &Organization{
				ID:     token.TokenID,
				Slug:   token.OrgSlug,
				Name:   token.Organization,
				Type:   "organization",
				Status: "active",
			}
		}
	}

	// Convert to slice and sort
	organizations := make([]Organization, 0, len(orgMap))
	for _, org := range orgMap {
		organizations = append(organizations, *org)
	}

	sort.Slice(organizations, func(i, j int) bool {
		return organizations[i].Slug < organizations[j].Slug
	})

	return organizations, nil
}

// CleanupUserKeychain removes all stored macaroons for a user
// Note: This doesn't delete the service itself (not possible with go-keyring),
// but deletes all known org keys. Individual keys may remain if we don't know about them.
func (m *Manager) CleanupUserKeychain(user *User) error {
	keychainService := buildUserKeychainService(user.ID)

	// We can't enumerate all keys in a service with go-keyring,
	// so we'll try to get organizations and delete their keys
	// This is best-effort cleanup

	// Try to fetch orgs to get a list of what to clean
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	// First, try to get a token to fetch orgs
	token, _, err := ReadFlyToken()
	if err == nil {
		orgs, err := m.FetchOrganizations(ctx, token)
		if err == nil {
			// Try to delete each org's macaroon
			for _, org := range orgs {
				keychainKey := buildFlyKeychainKey(org.Slug)
				// Ignore errors - key might not exist
				_ = keyring.Delete(keychainService, keychainKey)
			}
		}
	}

	// Also try to delete keys for orgs in the Sprites config
	if m.configMgr != nil {
		spritesOrgs := m.configMgr.GetOrgs()
		for orgName := range spritesOrgs {
			keychainKey := buildFlyKeychainKey(orgName)
			// Ignore errors - key might not exist
			_ = keyring.Delete(keychainService, keychainKey)
		}
	}

	return nil
}

// buildUserKeychainService creates a user-scoped keychain service name
// Uses user ID (not email) since emails can change
func buildUserKeychainService(userID string) string {
	return fmt.Sprintf("%s:%s", KeyringServicePrefix, userID)
}

// buildFlyKeychainKey creates a keychain key for storing Fly org tokens
func buildFlyKeychainKey(orgSlug string) string {
	return fmt.Sprintf("fly:%s", orgSlug)
}

// getHostname returns a hostname for CLI sessions
func getHostname() (string, error) {
	hostname, err := exec.Command("hostname").Output()
	if err != nil {
		return "", err
	}
	return strings.TrimSpace(string(hostname)), nil
}

// openBrowser opens a URL in the default browser
func openBrowser(url string) error {
	var cmd string
	var args []string

	switch runtime.GOOS {
	case "darwin":
		cmd = "open"
		args = []string{url}
	case "linux":
		cmd = "xdg-open"
		args = []string{url}
	case "windows":
		cmd = "cmd"
		args = []string{"/c", "start", url}
	default:
		return fmt.Errorf("unsupported platform: %s", runtime.GOOS)
	}

	return exec.Command(cmd, args...).Start()
}
