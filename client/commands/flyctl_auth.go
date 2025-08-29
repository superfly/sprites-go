package commands

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"strings"
	"time"

	"gopkg.in/yaml.v3"

	"github.com/superfly/sprite-env/client/prompts"
)

// FlyTokenInfo represents a token info from the current tokens endpoint
type FlyTokenInfo struct {
	Organization string `json:"organization"`
	OrgSlug      string `json:"org_slug"`
	TokenID      string `json:"token_id"`
	User         string `json:"user"`
}

// FlyTokensResponse represents the response from the current tokens endpoint
type FlyTokensResponse struct {
	Tokens []FlyTokenInfo `json:"tokens"`
}

// FlyOrganization represents a Fly.io organization
type FlyOrganization struct {
	ID     string `json:"id"`
	Slug   string `json:"slug"`
	Name   string `json:"name"`
	Type   string `json:"type"`
	Status string `json:"status"`
}

// FlyOrganizationsResponse represents the response from listing organizations
type FlyOrganizationsResponse struct {
	Organizations []FlyOrganization `json:"organizations"`
}

// FlyTokenRequest represents the request to create a sprite token
type FlyTokenRequest struct {
	Description string `json:"description,omitempty"`
	InviteCode  string `json:"invite_code,omitempty"`
}

// FlyTokenResponse represents the response from creating a sprite token
type FlyTokenResponse struct {
	Token string `json:"token"`
}

// GetFlyToken returns the Fly.io access token from the config file or environment
// Returns the token and the source (either env var name or config file path)
func GetFlyToken() (string, string, error) {
	// Check environment variables first (higher priority)
	if token := os.Getenv("FLY_ACCESS_TOKEN"); token != "" {
		slog.Debug("Found Fly token in environment", "source", "FLY_ACCESS_TOKEN", "token_prefix", token[:10]+"...")
		return token, "FLY_ACCESS_TOKEN", nil
	}
	if token := os.Getenv("FLY_API_TOKEN"); token != "" {
		slog.Debug("Found Fly token in environment", "source", "FLY_API_TOKEN", "token_prefix", token[:10]+"...")
		return token, "FLY_API_TOKEN", nil
	}

	// Get config directory
	configDir := os.Getenv("FLY_CONFIG_DIR")
	if configDir == "" {
		homeDir, err := os.UserHomeDir()
		if err != nil {
			slog.Debug("Failed to get home directory", "error", err)
			return "", "", fmt.Errorf("failed to get home directory: %w", err)
		}
		configDir = filepath.Join(homeDir, ".fly")
	}
	slog.Debug("Using Fly config directory", "path", configDir)

	// Read config file
	configPath := filepath.Join(configDir, "config.yml")
	slog.Debug("Reading Fly config file", "path", configPath)

	data, err := os.ReadFile(configPath)
	if err != nil {
		slog.Debug("Failed to read Fly config file", "path", configPath, "error", err)
		return "", "", fmt.Errorf("failed to read config file: %w", err)
	}

	slog.Debug("Fly config file contents", "size", len(data))

	// Parse YAML to get token
	var config struct {
		AccessToken string `yaml:"access_token"`
	}

	if err := yaml.Unmarshal(data, &config); err != nil {
		slog.Debug("Failed to parse Fly config YAML", "error", err, "data", string(data))
		return "", "", fmt.Errorf("failed to parse config: %w", err)
	}

	if config.AccessToken == "" {
		slog.Debug("No access token found in Fly config", "config", config)
		return "", "", fmt.Errorf("no access token found in config")
	}

	slog.Debug("Found Fly token in config file", "token_prefix", config.AccessToken[:10]+"...", "token_length", len(config.AccessToken))
	return config.AccessToken, configPath, nil
}

// CheckFlyctlInstalled checks if flyctl is installed
func CheckFlyctlInstalled() bool {
	_, err := exec.LookPath("flyctl")
	if err != nil {
		// Also check for "fly" as an alias
		_, err = exec.LookPath("fly")
		return err == nil
	}
	return true
}

// FetchFlyOrganizations fetches the list of organizations from Fly.io API
func FetchFlyOrganizations(token string) ([]FlyOrganization, error) {
	// Use api.machines.dev to get the current user's tokens and organizations
	url := "https://api.machines.dev/v1/tokens/current"

	httpReq, err := http.NewRequest("GET", url, nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	authHeader := "FlyV1 " + token
	httpReq.Header.Set("Authorization", authHeader)

	// Debug logging
	slog.Debug("Fly API request",
		"method", httpReq.Method,
		"url", url,
		"authorization", authHeader)

	client := &http.Client{Timeout: 30 * time.Second}
	resp, err := client.Do(httpReq)
	if err != nil {
		slog.Debug("Fly API request failed", "error", err)
		return nil, fmt.Errorf("failed to fetch organizations: %w", err)
	}
	defer resp.Body.Close()

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, fmt.Errorf("failed to read response: %w", err)
	}

	// Debug logging of response
	slog.Debug("Fly API response",
		"status", resp.StatusCode,
		"body", string(body))

	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("API returned status %d: %s", resp.StatusCode, string(body))
	}

	var tokensResp FlyTokensResponse
	if err := json.Unmarshal(body, &tokensResp); err != nil {
		slog.Debug("Failed to parse tokens response", "error", err, "body", string(body))
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	// Convert token info to organizations
	// Use a map to deduplicate organizations (user may have multiple tokens per org)
	orgMap := make(map[string]*FlyOrganization)
	for _, token := range tokensResp.Tokens {
		if _, exists := orgMap[token.OrgSlug]; !exists {
			orgMap[token.OrgSlug] = &FlyOrganization{
				ID:     token.TokenID, // Using token ID as org ID since we don't have the actual org ID
				Slug:   token.OrgSlug,
				Name:   token.Organization,
				Type:   "organization", // Default type
				Status: "active",       // Default status
			}
		}
	}

	// Convert map to slice
	organizations := make([]FlyOrganization, 0, len(orgMap))
	for _, org := range orgMap {
		organizations = append(organizations, *org)
	}

	// Sort organizations by slug
	sort.Slice(organizations, func(i, j int) bool {
		return organizations[i].Slug < organizations[j].Slug
	})

	slog.Debug("Parsed organizations", "count", len(organizations))
	for i, org := range organizations {
		slog.Debug("Organization",
			"index", i,
			"id", org.ID,
			"slug", org.Slug,
			"name", org.Name,
			"type", org.Type,
			"status", org.Status)
	}

	return organizations, nil
}

// CreateSpriteToken creates a sprite token for the selected organization
func CreateSpriteToken(flyToken string, orgSlug string) (string, error) {
	// Get API URL from environment or use default
	apiURL := "https://api.sprites.dev"
	if envURL := os.Getenv("SPRITES_API_URL"); envURL != "" {
		apiURL = strings.TrimRight(envURL, "/")
	}

	// Use the API URL to create organization-specific sprite tokens
	url := fmt.Sprintf("%s/v1/organizations/%s/tokens", apiURL, orgSlug)

	// First attempt without invite code
	token, statusCode, err := createSpriteTokenWithInvite(flyToken, url, "")
	if err != nil {
		// Check if the error indicates sprites not enabled (401) or forbidden (403)
		if statusCode == http.StatusUnauthorized && strings.Contains(err.Error(), "Sprites not enabled") {
			slog.Debug("Organization requires invite code - Sprites not enabled", "status", statusCode)

			// Prompt for invite code
			inviteCode, promptErr := prompts.PromptForInviteCode()
			if promptErr != nil {
				return "", fmt.Errorf("organization requires an invite code: %w", promptErr)
			}

			// Retry with invite code
			token, _, err = createSpriteTokenWithInvite(flyToken, url, inviteCode)
			if err != nil {
				return "", fmt.Errorf("failed to create token with invite code: %w", err)
			}
			return token, nil
		} else if statusCode == http.StatusForbidden {
			slog.Debug("Organization requires invite code - Forbidden", "status", statusCode)

			// Prompt for invite code
			inviteCode, promptErr := prompts.PromptForInviteCode()
			if promptErr != nil {
				return "", fmt.Errorf("organization requires an invite code: %w", promptErr)
			}

			// Retry with invite code
			token, _, err = createSpriteTokenWithInvite(flyToken, url, inviteCode)
			if err != nil {
				return "", fmt.Errorf("failed to create token with invite code: %w", err)
			}
			return token, nil
		}
		return "", err
	}

	return token, nil
}

// createSpriteTokenWithInvite performs the actual API request to create a token
func createSpriteTokenWithInvite(flyToken string, url string, inviteCode string) (string, int, error) {
	// Create request body
	req := FlyTokenRequest{
		Description: "Sprite CLI Token",
	}
	if inviteCode != "" {
		req.InviteCode = inviteCode
	}

	jsonData, err := json.Marshal(req)
	if err != nil {
		return "", 0, fmt.Errorf("failed to marshal request: %w", err)
	}

	httpReq, err := http.NewRequest("POST", url, bytes.NewReader(jsonData))
	if err != nil {
		return "", 0, fmt.Errorf("failed to create request: %w", err)
	}

	authHeader := "FlyV1 " + flyToken
	httpReq.Header.Set("Authorization", authHeader)
	httpReq.Header.Set("Content-Type", "application/json")

	// Debug logging
	slog.Debug("Fly API request",
		"method", httpReq.Method,
		"url", url,
		"authorization", authHeader,
		"body", string(jsonData))

	client := &http.Client{Timeout: 30 * time.Second}
	resp, err := client.Do(httpReq)
	if err != nil {
		slog.Debug("Fly API request failed", "error", err)
		return "", 0, fmt.Errorf("failed to create token: %w", err)
	}
	defer resp.Body.Close()

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return "", resp.StatusCode, fmt.Errorf("failed to read response: %w", err)
	}

	// Debug logging of response
	slog.Debug("Fly API response",
		"status", resp.StatusCode,
		"body", string(body))

	if resp.StatusCode != http.StatusOK && resp.StatusCode != http.StatusCreated {
		return "", resp.StatusCode, fmt.Errorf("API returned status %d: %s", resp.StatusCode, string(body))
	}

	var tokenResp FlyTokenResponse
	if err := json.Unmarshal(body, &tokenResp); err != nil {
		slog.Debug("Failed to parse token response", "error", err, "body", string(body))
		return "", resp.StatusCode, fmt.Errorf("failed to parse response: %w", err)
	}

	if tokenResp.Token == "" {
		slog.Debug("Empty token in response", "response", tokenResp)
		return "", resp.StatusCode, fmt.Errorf("no token returned in response")
	}

	// Log token details (careful not to log the full token in production)
	slog.Debug("Token created",
		"token_prefix", tokenResp.Token[:10]+"...",
		"token_length", len(tokenResp.Token))

	return tokenResp.Token, resp.StatusCode, nil
}
