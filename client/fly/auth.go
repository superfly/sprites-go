package fly

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net/http"
	"os"
	"path/filepath"
	"strings"
	"time"

	"github.com/zalando/go-keyring"
	"gopkg.in/yaml.v3"
)

const (
	baseURL             = "https://api.fly.io"
	FlyKeyringService   = "sprites-cli"
	FlyKeyringKeyPrefix = "fly-token"
)

var (
	ErrNoToken      = errors.New("no Fly.io token found")
	ErrNotFound     = errors.New("not found")
	ErrUnknown      = errors.New("unknown error")
	ErrLoginExpired = errors.New("login expired, please try again")
	ErrLoginFailed  = errors.New("failed to log in, please try again")
	ErrInvalidCreds = errors.New("incorrect email and password combination")
)

// CLISession represents a CLI authentication session
type CLISession struct {
	ID          string                 `json:"id"`
	URL         string                 `json:"auth_url,omitempty"`
	AccessToken string                 `json:"access_token,omitempty"`
	Metadata    map[string]interface{} `json:"metadata,omitempty"`
}

// FlyConfig represents the Fly.io config file structure
type FlyConfig struct {
	AccessToken string `yaml:"access_token"`
}

// GetFlyConfigPath returns the path to the Fly.io config file
func GetFlyConfigPath() (string, error) {
	configDir := os.Getenv("FLY_CONFIG_DIR")
	if configDir == "" {
		homeDir, err := os.UserHomeDir()
		if err != nil {
			return "", fmt.Errorf("failed to get home directory: %w", err)
		}
		configDir = filepath.Join(homeDir, ".fly")
	}
	return filepath.Join(configDir, "config.yml"), nil
}

// NOTE: Fly tokens are NOT stored in the keyring because they can be very large
// (especially macaroons which can contain multiple tokens). System keyrings typically
// have a 2-4KB limit. Instead, Fly tokens are managed by flyctl in ~/.fly/config.yml
// and we only store the smaller Sprite org tokens in the keyring.
//
// The functions below are kept for reference but are not used in production.

// StoreFlyTokenInKeyring stores a Fly.io token in the user-scoped keyring
// WARNING: This will fail for large tokens (>2KB). Use ~/.fly/config.yml instead.
func StoreFlyTokenInKeyring(userID, token string) error {
	keyringService := fmt.Sprintf("%s:%s", FlyKeyringService, userID)
	keyringKey := fmt.Sprintf("%s:%s", FlyKeyringKeyPrefix, userID)
	return keyring.Set(keyringService, keyringKey, token)
}

// ReadFlyTokenFromKeyring reads the Fly.io token from the user-scoped keyring
// NOTE: In practice, tokens should be read from ~/.fly/config.yml
func ReadFlyTokenFromKeyring(userID string) (string, error) {
	keyringService := fmt.Sprintf("%s:%s", FlyKeyringService, userID)
	keyringKey := fmt.Sprintf("%s:%s", FlyKeyringKeyPrefix, userID)
	token, err := keyring.Get(keyringService, keyringKey)
	if err != nil {
		return "", ErrNoToken
	}
	return token, nil
}

// DeleteFlyTokenFromKeyring deletes the Fly.io token from the user-scoped keyring
// NOTE: In practice, tokens should be managed via flyctl
func DeleteFlyTokenFromKeyring(userID string) error {
	keyringService := fmt.Sprintf("%s:%s", FlyKeyringService, userID)
	keyringKey := fmt.Sprintf("%s:%s", FlyKeyringKeyPrefix, userID)
	return keyring.Delete(keyringService, keyringKey)
}

// ReadFlyToken reads the Fly.io token from keyring first, then falls back to config file
func ReadFlyToken() (string, string, error) {
	// First, try to read from config file to get backward compatibility
	configPath, err := GetFlyConfigPath()
	if err != nil {
		return "", "", err
	}

	data, err := os.ReadFile(configPath)
	if err != nil {
		if os.IsNotExist(err) {
			return "", "", ErrNoToken
		}
		return "", "", fmt.Errorf("failed to read config file: %w", err)
	}

	var config FlyConfig
	if err := yaml.Unmarshal(data, &config); err != nil {
		return "", "", fmt.Errorf("failed to parse config: %w", err)
	}

	if config.AccessToken == "" {
		return "", "", ErrNoToken
	}

	return config.AccessToken, configPath, nil
}

// ReadFlyTokenForUser reads the Fly.io token for a specific user from encrypted storage
func ReadFlyTokenForUser(userID string) (string, error) {
	// Try encrypted storage first
	token, err := ReadFlyTokenEncrypted(userID)
	if err == nil && token != "" {
		return token, nil
	}

	// Fall back to keyring (legacy, for migration)
	token, err = ReadFlyTokenFromKeyring(userID)
	if err == nil && token != "" {
		return token, nil
	}

	return "", ErrNoToken
}

// IsMacaroon checks if a token is a macaroon (starts with fm1r_ or fm2_)
func IsMacaroon(token string) bool {
	for _, tok := range strings.Split(token, ",") {
		pfx, _, _ := strings.Cut(tok, "_")
		switch pfx {
		case "fm1r", "fm2":
			return true
		}
	}
	return false
}

// StartCLISession starts a CLI authentication session
func StartCLISession(sessionName string, args map[string]interface{}) (*CLISession, error) {
	if args == nil {
		args = make(map[string]interface{})
	}
	args["name"] = sessionName

	postData, err := json.Marshal(args)
	if err != nil {
		return nil, fmt.Errorf("failed to marshal request: %w", err)
	}

	url := fmt.Sprintf("%s/api/v1/cli_sessions", baseURL)

	resp, err := http.Post(url, "application/json", bytes.NewBuffer(postData))
	if err != nil {
		return nil, fmt.Errorf("failed to start CLI session: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusCreated {
		body, _ := io.ReadAll(resp.Body)
		return nil, fmt.Errorf("unexpected status %d: %s", resp.StatusCode, string(body))
	}

	var result CLISession
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return nil, fmt.Errorf("failed to decode response: %w", err)
	}

	return &result, nil
}

// GetCLISessionState retrieves the current state of a CLI session
func GetCLISessionState(ctx context.Context, id string) (*CLISession, error) {
	url := fmt.Sprintf("%s/api/v1/cli_sessions/%s", baseURL, id)

	req, err := http.NewRequestWithContext(ctx, http.MethodGet, url, nil)
	if err != nil {
		return nil, err
	}

	res, err := http.DefaultClient.Do(req)
	if err != nil {
		return nil, err
	}
	defer res.Body.Close()

	switch res.StatusCode {
	case http.StatusOK:
		var auth CLISession
		if err := json.NewDecoder(res.Body).Decode(&auth); err != nil {
			return nil, fmt.Errorf("failed to decode session: %w", err)
		}
		return &auth, nil
	case http.StatusNotFound:
		return nil, ErrNotFound
	default:
		return nil, ErrUnknown
	}
}

// GetAccessTokenForCLISession polls for the access token from a CLI session
func GetAccessTokenForCLISession(ctx context.Context, id string) (string, error) {
	val, err := GetCLISessionState(ctx, id)
	if err != nil {
		return "", err
	}
	return val.AccessToken, nil
}

// WaitForCLISession waits for a CLI session to complete and returns the token
func WaitForCLISession(ctx context.Context, id string) (string, error) {
	ctx, cancel := context.WithTimeout(ctx, 15*time.Minute)
	defer cancel()

	ticker := time.NewTicker(1 * time.Second)
	defer ticker.Stop()

	for {
		select {
		case <-ctx.Done():
			if errors.Is(ctx.Err(), context.DeadlineExceeded) {
				return "", ErrLoginExpired
			}
			return "", ctx.Err()
		case <-ticker.C:
			token, err := GetAccessTokenForCLISession(ctx, id)
			if err != nil {
				continue
			}
			if token != "" {
				return token, nil
			}
		}
	}
}

// GetAccessToken performs email/password authentication
func GetAccessToken(ctx context.Context, email, password, otp string) (string, error) {
	var postData bytes.Buffer
	if err := json.NewEncoder(&postData).Encode(map[string]interface{}{
		"data": map[string]interface{}{
			"attributes": map[string]string{
				"email":    email,
				"password": password,
				"otp":      otp,
			},
		},
	}); err != nil {
		return "", err
	}

	url := fmt.Sprintf("%s/api/v1/sessions", baseURL)

	req, err := http.NewRequestWithContext(ctx, http.MethodPost, url, &postData)
	if err != nil {
		return "", err
	}
	req.Header.Set("Content-Type", "application/json")

	res, err := http.DefaultClient.Do(req)
	if err != nil {
		return "", err
	}
	defer res.Body.Close()

	switch {
	case res.StatusCode >= http.StatusInternalServerError:
		return "", errors.New("an unknown server error occurred, please try again")
	case res.StatusCode >= http.StatusBadRequest:
		return "", ErrInvalidCreds
	default:
		var result map[string]map[string]map[string]string
		if err := json.NewDecoder(res.Body).Decode(&result); err != nil {
			return "", err
		}
		return result["data"]["attributes"]["access_token"], nil
	}
}

// User represents a Fly.io user
type User struct {
	ID    string `json:"id"`
	Email string `json:"email"`
	Name  string `json:"name"`
}

// GetCurrentUser fetches the current user info from a Fly token
func GetCurrentUser(ctx context.Context, token string) (*User, error) {
	url := "https://api.fly.io/graphql"

	query := `{"query":"query { viewer { id email name } }"}`

	req, err := http.NewRequestWithContext(ctx, http.MethodPost, url, strings.NewReader(query))
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	req.Header.Set("Authorization", AuthorizationHeader(token))
	req.Header.Set("Content-Type", "application/json")

	client := &http.Client{Timeout: 10 * time.Second}
	resp, err := client.Do(req)
	if err != nil {
		return nil, fmt.Errorf("failed to fetch user: %w", err)
	}
	defer resp.Body.Close()

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, fmt.Errorf("failed to read response: %w", err)
	}

	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("user fetch failed with status %d: %s", resp.StatusCode, string(body))
	}

	var result struct {
		Data struct {
			Viewer User `json:"viewer"`
		} `json:"data"`
	}
	if err := json.Unmarshal(body, &result); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	if result.Data.Viewer.ID == "" {
		return nil, errors.New("no user ID in response")
	}
	if result.Data.Viewer.Email == "" {
		return nil, errors.New("no user email in response")
	}

	return &result.Data.Viewer, nil
}

// ExchangeForMacaroon exchanges a token for a macaroon via the Sprites API
// This is done by creating a sprite token which is a macaroon
func ExchangeForMacaroon(ctx context.Context, flyToken string, orgSlug string) (string, error) {
	url := fmt.Sprintf("https://api.machines.dev/v1/organizations/%s/sprites/tokens", orgSlug)

	req, err := http.NewRequestWithContext(ctx, http.MethodPost, url, nil)
	if err != nil {
		return "", fmt.Errorf("failed to create request: %w", err)
	}

	// Use FlyV1 auth header format
	authHeader := "FlyV1 " + flyToken
	req.Header.Set("Authorization", authHeader)
	req.Header.Set("Content-Type", "application/json")

	client := &http.Client{Timeout: 30 * time.Second}
	resp, err := client.Do(req)
	if err != nil {
		return "", fmt.Errorf("failed to exchange token: %w", err)
	}
	defer resp.Body.Close()

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return "", fmt.Errorf("failed to read response: %w", err)
	}

	if resp.StatusCode != http.StatusOK && resp.StatusCode != http.StatusCreated {
		return "", fmt.Errorf("token exchange failed with status %d: %s", resp.StatusCode, string(body))
	}

	var result struct {
		Token string `json:"token"`
	}
	if err := json.Unmarshal(body, &result); err != nil {
		return "", fmt.Errorf("failed to parse response: %w", err)
	}

	if result.Token == "" {
		return "", errors.New("no token in response")
	}

	return result.Token, nil
}

// ClearFlyToken removes the Fly.io token from ~/.fly/config.yml
func ClearFlyToken() error {
	configPath, err := GetFlyConfigPath()
	if err != nil {
		return err
	}

	// Check if file exists
	if _, err := os.Stat(configPath); os.IsNotExist(err) {
		return nil // Nothing to delete
	}

	// Remove the file
	if err := os.Remove(configPath); err != nil {
		return fmt.Errorf("failed to remove config file: %w", err)
	}

	return nil
}

// AuthorizationHeader returns the appropriate authorization header for a token
func AuthorizationHeader(token string) string {
	for _, tok := range strings.Split(token, ",") {
		pfx, _, _ := strings.Cut(tok, "_")
		switch pfx {
		case "fm1r", "fm2":
			return "FlyV1 " + token
		}
	}
	return "Bearer " + token
}
