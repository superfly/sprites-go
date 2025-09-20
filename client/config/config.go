package config

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"runtime"
	"strings"

	v1 "github.com/superfly/sprite-env/client/config/v1"
	"github.com/zalando/go-keyring"
)

const (
	KeyringService = "sprites-cli"
)

// Manager manages sprite configuration
type Manager struct {
	configPath string
	config     *v1.Config
}

// buildKeychainKeyV1 creates the new keychain key format for v1
func buildKeychainKeyV1(url, org, sprite string) string {
	// Clean the URL to make it a valid keychain key
	cleanURL := strings.ReplaceAll(url, "://", "-")
	cleanURL = strings.ReplaceAll(cleanURL, ":", "-")
	cleanURL = strings.ReplaceAll(cleanURL, "/", "-")
	cleanURL = strings.TrimSuffix(cleanURL, "-")

	// For org-level keys (when sprite is empty), use a two-part format
	if sprite == "" {
		return fmt.Sprintf("%s:%s", cleanURL, org)
	}
	return fmt.Sprintf("%s:%s:%s", cleanURL, org, sprite)
}

// NewManager creates a new configuration manager that uses sprites.json (creating it from config.json if needed)
// Note: This manager reads and writes to sprites.json. The config.json file is preserved for backward compatibility
// with old clients, but is not updated by this manager.
func NewManager() (*Manager, error) {
	configDir, err := getConfigDir()
	if err != nil {
		return nil, fmt.Errorf("failed to get config directory: %w", err)
	}

	// Perform migration if needed (creates sprites.json from config.json if it doesn't exist)
	if err := performMigrationIfNeeded(configDir); err != nil {
		return nil, fmt.Errorf("migration failed: %w", err)
	}

	configPath := filepath.Join(configDir, "sprites.json")

	m := &Manager{
		configPath: configPath,
		config: &v1.Config{
			Version:    CurrentConfigVersion,
			URLs:       make(map[string]*v1.URLConfig),
			URLAliases: make(map[string]string),
		},
	}

	// Load config if it exists
	if data, err := os.ReadFile(configPath); err == nil {
		if err := json.Unmarshal(data, &m.config); err != nil {
			return nil, fmt.Errorf("failed to unmarshal sprites.json: %w", err)
		}
		// Ensure URLAliases is initialized for older configs
		if m.config.URLAliases == nil {
			m.config.URLAliases = make(map[string]string)
		}
	} else if !os.IsNotExist(err) {
		return nil, fmt.Errorf("failed to read sprites.json: %w", err)
	}

	return m, nil
}

// getConfigDir returns the appropriate config directory path
func getConfigDir() (string, error) {
	var homeDir string

	switch runtime.GOOS {
	case "windows":
		homeDir = os.Getenv("USERPROFILE")
		if homeDir == "" {
			homeDir = os.Getenv("HOMEDRIVE") + os.Getenv("HOMEPATH")
		}
	default:
		homeDir = os.Getenv("HOME")
	}

	if homeDir == "" {
		return "", fmt.Errorf("unable to determine home directory")
	}

	configDir := filepath.Join(homeDir, ".sprites")

	// Ensure directory exists
	if err := os.MkdirAll(configDir, 0700); err != nil {
		return "", fmt.Errorf("failed to create config directory: %w", err)
	}

	return configDir, nil
}

// Load reads the configuration from disk
func (m *Manager) Load() error {
	data, err := os.ReadFile(m.configPath)
	if err != nil {
		if os.IsNotExist(err) {
			// No config file yet, use defaults
			return nil
		}
		return fmt.Errorf("failed to read config file: %w", err)
	}

	// Check if we need to migrate
	migratedData, err := MigrateConfig(data)
	if err != nil {
		return fmt.Errorf("failed to migrate config: %w", err)
	}

	// Unmarshal the (possibly migrated) config
	if err := json.Unmarshal(migratedData, &m.config); err != nil {
		return fmt.Errorf("failed to unmarshal config: %w", err)
	}

	// Ensure URLAliases is initialized for older configs
	if m.config.URLAliases == nil {
		m.config.URLAliases = make(map[string]string)
	}

	// Save if we migrated
	if string(migratedData) != string(data) {
		if err := m.Save(); err != nil {
			return fmt.Errorf("failed to save migrated config: %w", err)
		}
	}

	return nil
}

// Save writes the configuration to disk
func (m *Manager) Save() error {
	// Ensure config directory exists
	dir := filepath.Dir(m.configPath)
	if err := os.MkdirAll(dir, 0700); err != nil {
		return fmt.Errorf("failed to create config directory: %w", err)
	}

	// Marshal config
	data, err := json.MarshalIndent(m.config, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal config: %w", err)
	}

	return os.WriteFile(m.configPath, data, 0600)
}

// GetCurrentOrgConfig returns the current organization configuration
func (m *Manager) GetCurrentOrgConfig() (*v1.OrgConfig, error) {
	if m.config.CurrentSelection == nil {
		return nil, fmt.Errorf("no current organization selected")
	}

	urlConfig, exists := m.config.URLs[m.config.CurrentSelection.URL]
	if !exists {
		return nil, fmt.Errorf("URL %s not found in config", m.config.CurrentSelection.URL)
	}

	orgConfig, exists := urlConfig.Orgs[m.config.CurrentSelection.Org]
	if !exists {
		return nil, fmt.Errorf("org %s not found under URL %s", m.config.CurrentSelection.Org, m.config.CurrentSelection.URL)
	}

	return orgConfig, nil
}

// GetCurrentOrgToken returns the token for the current organization
func (m *Manager) GetCurrentOrgToken() (string, error) {
	orgConfig, err := m.GetCurrentOrgConfig()
	if err != nil {
		return "", err
	}

	return m.getOrgToken(orgConfig)
}

// getOrgToken retrieves the token for an org, checking keyring first
func (m *Manager) getOrgToken(org *v1.OrgConfig) (string, error) {
	if !m.config.DisableKeyring && org.UseKeyring {
		// Try keyring first
		token, err := keyring.Get(KeyringService, org.KeychainKey)
		if err == nil && token != "" {
			return token, nil
		}
	}

	// Fallback to file-stored token
	if org.Token != "" {
		return org.Token, nil
	}

	return "", fmt.Errorf("no token found for org %s", org.Name)
}

// setOrgToken stores the token for an org
func (m *Manager) setOrgToken(org *v1.OrgConfig, token string) error {
	if token == "" {
		return fmt.Errorf("cannot store empty token for organization %s", org.Name)
	}

	if !m.config.DisableKeyring {
		// Try to store in keyring first
		err := keyring.Set(KeyringService, org.KeychainKey, token)
		if err == nil {
			// Successfully stored in keyring
			org.Token = "" // Clear file-stored token
			org.UseKeyring = true
			return nil
		}
	}

	// Keyring disabled or failed, use file storage
	org.Token = token
	org.UseKeyring = false
	return nil
}

// AddSprite adds a new sprite or updates an existing one
func (m *Manager) AddSprite(url, orgName, spriteName, token string) error {
	// Validate inputs
	if url == "" {
		return fmt.Errorf("URL cannot be empty")
	}
	if orgName == "" {
		return fmt.Errorf("organization name cannot be empty")
	}
	if spriteName == "" {
		return fmt.Errorf("sprite name cannot be empty")
	}

	// Ensure URL config exists
	if _, exists := m.config.URLs[url]; !exists {
		m.config.URLs[url] = &v1.URLConfig{
			URL:  url,
			Orgs: make(map[string]*v1.OrgConfig),
		}
	}

	// Ensure org config exists
	urlConfig := m.config.URLs[url]
	orgConfig, orgExists := urlConfig.Orgs[orgName]
	if !orgExists {
		// New org - create keychain key
		orgConfig = &v1.OrgConfig{
			Name:        orgName,
			KeychainKey: buildKeychainKeyV1(url, orgName, ""),
			Sprites:     make(map[string]*v1.SpriteConfig),
		}
		urlConfig.Orgs[orgName] = orgConfig
	}

	// Create or update sprite
	sprite, spriteExists := orgConfig.Sprites[spriteName]
	if !spriteExists {
		sprite = &v1.SpriteConfig{
			Name: spriteName,
		}
	}

	// Set the token at the org level
	if err := m.setOrgToken(orgConfig, token); err != nil {
		return err
	}

	orgConfig.Sprites[spriteName] = sprite

	// Set as current if it's the first org
	if m.config.CurrentSelection == nil {
		m.config.CurrentSelection = &v1.CurrentSelection{
			URL: url,
			Org: orgName,
		}
	}

	return m.Save()
}

// RemoveSprite removes a sprite
func (m *Manager) RemoveSprite(url, orgName, spriteName string) error {
	urlConfig, exists := m.config.URLs[url]
	if !exists {
		return fmt.Errorf("URL %s not found", url)
	}

	orgConfig, exists := urlConfig.Orgs[orgName]
	if !exists {
		return fmt.Errorf("org %s not found under URL %s", orgName, url)
	}

	if _, exists := orgConfig.Sprites[spriteName]; !exists {
		return fmt.Errorf("sprite %s not found under org %s", spriteName, orgName)
	}

	// Remove the sprite
	delete(orgConfig.Sprites, spriteName)

	// If org has no more sprites, remove it and clean up token
	if len(orgConfig.Sprites) == 0 {
		// Delete token from keyring if it was stored there
		if orgConfig.UseKeyring {
			_ = keyring.Delete(KeyringService, orgConfig.KeychainKey)
		}
		delete(urlConfig.Orgs, orgName)
	}

	// If URL has no more orgs, remove it
	if len(urlConfig.Orgs) == 0 {
		delete(m.config.URLs, url)
	}

	// Clear current selection if we removed the last sprite from the current org
	if m.config.CurrentSelection != nil &&
		m.config.CurrentSelection.URL == url &&
		m.config.CurrentSelection.Org == orgName &&
		len(orgConfig.Sprites) == 0 {
		m.config.CurrentSelection = nil
	}

	return m.Save()
}

// GetAllSprites returns all sprites organized by URL and org
func (m *Manager) GetAllSprites() map[string]*v1.URLConfig {
	return m.config.URLs
}

// FindSprite finds a sprite by name, handling conflicts
func (m *Manager) FindSprite(spriteName string) (*v1.SpriteConfig, string, string, string, error) {
	var foundSprites []struct {
		sprite *v1.SpriteConfig
		url    string
		org    string
	}

	// Search all URLs and orgs
	for url, urlConfig := range m.config.URLs {
		for orgName, orgConfig := range urlConfig.Orgs {
			if sprite, exists := orgConfig.Sprites[spriteName]; exists {
				foundSprites = append(foundSprites, struct {
					sprite *v1.SpriteConfig
					url    string
					org    string
				}{
					sprite: sprite,
					url:    url,
					org:    orgName,
				})
			}
		}
	}

	if len(foundSprites) == 0 {
		return nil, "", "", "", fmt.Errorf("sprite %s not found", spriteName)
	}

	if len(foundSprites) == 1 {
		return foundSprites[0].sprite, foundSprites[0].url, foundSprites[0].org, spriteName, nil
	}

	// Multiple sprites found - handle conflict
	fmt.Printf("Warning: Multiple sprites named '%s' found. ", spriteName)

	// If we have a current selection, prefer sprites from the same URL
	if m.config.CurrentSelection != nil {
		for _, found := range foundSprites {
			if found.url == m.config.CurrentSelection.URL {
				fmt.Printf("Using the one from URL %s\n", found.url)
				return found.sprite, found.url, found.org, spriteName, nil
			}
		}
	}

	// Default to first one
	fmt.Printf("Using the one from URL %s\n", foundSprites[0].url)
	return foundSprites[0].sprite, foundSprites[0].url, foundSprites[0].org, spriteName, nil
}

// IsKeyringDisabled returns whether keyring usage is disabled
func (m *Manager) IsKeyringDisabled() bool {
	return m.config.DisableKeyring
}

// SetKeyringDisabled enables or disables keyring usage
func (m *Manager) SetKeyringDisabled(disabled bool) error {
	m.config.DisableKeyring = disabled
	return m.Save()
}

// GetLastVersionCheck returns the last version check time
func (m *Manager) GetLastVersionCheck() string {
	return m.config.LastVersionCheck
}

// SetLastVersionCheck sets the last version check time
func (m *Manager) SetLastVersionCheck(timestamp string) {
	m.config.LastVersionCheck = timestamp
}

// GetLatestVersion returns the latest version
func (m *Manager) GetLatestVersion() string {
	return m.config.LatestVersion
}

// SetLatestVersion sets the latest version
func (m *Manager) SetLatestVersion(version string) {
	m.config.LatestVersion = version
}

// GetCurrentVersion returns the current version
func (m *Manager) GetCurrentVersion() string {
	return m.config.CurrentVersion
}

// SetCurrentVersion sets the current version
func (m *Manager) SetCurrentVersion(version string) {
	m.config.CurrentVersion = version
}

// ParseOrgWithAlias parses an org string that may contain an alias prefix (e.g., "alias:org")
// Returns: (parsedOrg, alias, hasAlias)
func (m *Manager) ParseOrgWithAlias(orgString string) (string, string, bool) {
	parts := strings.SplitN(orgString, ":", 2)
	if len(parts) == 2 {
		// Format is "alias:org"
		return parts[1], parts[0], true
	}
	// No alias present
	return orgString, "", false
}

// GetURLForAlias returns the URL associated with an alias
func (m *Manager) GetURLForAlias(alias string) (string, bool) {
	if m.config.URLAliases == nil {
		return "", false
	}
	url, exists := m.config.URLAliases[alias]
	return url, exists
}

// SetURLAlias sets or updates an alias for a URL
func (m *Manager) SetURLAlias(alias, url string) error {
	if m.config.URLAliases == nil {
		m.config.URLAliases = make(map[string]string)
	}
	m.config.URLAliases[alias] = url
	return m.Save()
}

// GetAllURLs returns all configured URLs (both from URLs map and aliases)
func (m *Manager) GetAllURLs() []string {
	urlSet := make(map[string]bool)

	// Add URLs from the URLs map
	for url := range m.config.URLs {
		urlSet[url] = true
	}

	// Add URLs from aliases
	for _, url := range m.config.URLAliases {
		urlSet[url] = true
	}

	// Convert to slice
	urls := make([]string, 0, len(urlSet))
	for url := range urlSet {
		urls = append(urls, url)
	}

	return urls
}
