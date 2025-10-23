package config

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"log/slog"
	"os"
	"path/filepath"
	"runtime"
	"strings"
	"time"

	v1 "github.com/superfly/sprite-env/client/config/v1"
	"github.com/superfly/sprite-env/client/keyring"
)

const (
	KeyringService = "sprites-cli"
)

// hashUserID creates a lowercase hex hash of the userID for safe filenames
func hashUserID(userID string) string {
	hash := sha256.Sum256([]byte(userID))
	hexHash := hex.EncodeToString(hash[:])
	return strings.ToLower(hexHash[:16])
}

// getUserConfigPath returns the path to a user's config file
func getUserConfigPath(userID string) (string, error) {
	configDir, err := getConfigDir()
	if err != nil {
		return "", err
	}

	usersDir := filepath.Join(configDir, "users")
	if err := os.MkdirAll(usersDir, 0700); err != nil {
		return "", fmt.Errorf("failed to create users directory: %w", err)
	}

	hash := hashUserID(userID)
	filename := fmt.Sprintf("%s-%s.json", userID, hash)
	return filepath.Join(usersDir, filename), nil
}

// Manager manages sprite configuration
type Manager struct {
	configPath    string
	config        *v1.Config
	userConfig    *v1.Config // Config loaded from user-specific file
	currentUserID string     // Cached current user ID
}

// buildKeyringKeyV1 creates the new keyring key format for v1
func buildKeyringKeyV1(url, org, sprite string) string {
	// Clean the URL to make it a valid keyring key
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
			Users:      make([]*v1.UserInfo, 0),
		},
	}

	// Load config if it exists
	if data, err := os.ReadFile(configPath); err == nil {
		// Check if migration is needed
		version := DetectConfigVersion(data)
		if version != CurrentConfigVersion {
			fmt.Printf("Configuration version %s detected. Migrating to version %s...\n", version, CurrentConfigVersion)

			// Create backup with timestamp
			timestamp := time.Now().Format("20060102-150405")
			backupPath := fmt.Sprintf("%s.backup-%s", configPath, timestamp)
			if err := os.WriteFile(backupPath, data, 0600); err != nil {
				return nil, fmt.Errorf("failed to create backup: %w", err)
			}
			fmt.Printf("✓ Backup created: %s\n", backupPath)

			// Migrate config
			migratedData, err := MigrateConfig(data)
			if err != nil {
				return nil, fmt.Errorf("failed to migrate config: %w", err)
			}

			// Write migrated config back
			if err := os.WriteFile(configPath, migratedData, 0600); err != nil {
				return nil, fmt.Errorf("failed to write migrated config: %w", err)
			}
			data = migratedData
			fmt.Println("✓ Configuration migrated successfully")
		}

		if err := json.Unmarshal(data, &m.config); err != nil {
			return nil, fmt.Errorf("failed to unmarshal sprites.json: %w", err)
		}
		// Ensure URLAliases is initialized for older configs
		if m.config.URLAliases == nil {
			m.config.URLAliases = make(map[string]string)
		}
		// Ensure Users is initialized for older configs
		if m.config.Users == nil {
			m.config.Users = make([]*v1.UserInfo, 0)
		}

		// Load user-specific config if current user is set
		if m.config.CurrentUser != "" {
			if err := m.loadUserConfig(m.config.CurrentUser); err != nil {
				slog.Debug("Failed to load user config", "userID", m.config.CurrentUser, "error", err)
			}
		}

		// Migrate any tokens from config to keyring
		if err := m.MigrateTokensToKeyring(); err != nil {
			slog.Warn("Failed to migrate tokens to keyring", "error", err)
			// Don't fail on migration errors, just log them
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

	// Clean config before saving (remove tokens and UseKeyring flags)
	cleanConfigBeforeSave(m.config)

	// Marshal config
	data, err := json.MarshalIndent(m.config, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal config: %w", err)
	}

	if err := os.WriteFile(m.configPath, data, 0600); err != nil {
		return err
	}

	// Also save user config if we have one loaded
	if m.userConfig != nil && m.currentUserID != "" {
		return m.saveUserConfig(m.currentUserID)
	}

	return nil
}

// loadUserConfig loads a user-specific config file
func (m *Manager) loadUserConfig(userID string) error {
	userConfigPath, err := getUserConfigPath(userID)
	if err != nil {
		return err
	}

	data, err := os.ReadFile(userConfigPath)
	if err != nil {
		if os.IsNotExist(err) {
			// No user config yet, create an empty one
			m.userConfig = &v1.Config{
				Version:    CurrentConfigVersion,
				URLs:       make(map[string]*v1.URLConfig),
				URLAliases: make(map[string]string),
			}
			m.currentUserID = userID
			slog.Debug("Created new user config", "userID", userID)
			return nil
		}
		return fmt.Errorf("failed to read user config: %w", err)
	}

	var userCfg v1.Config
	if err := json.Unmarshal(data, &userCfg); err != nil {
		return fmt.Errorf("failed to unmarshal user config: %w", err)
	}

	m.userConfig = &userCfg
	m.currentUserID = userID

	slog.Debug("Loaded user config",
		"userID", userID,
		"urls", len(userCfg.URLs))

	return nil
}

// saveUserConfig saves the user-specific config file
func (m *Manager) saveUserConfig(userID string) error {
	if m.userConfig == nil {
		return fmt.Errorf("no user config to save")
	}

	userConfigPath, err := getUserConfigPath(userID)
	if err != nil {
		return err
	}

	// Clean user config before saving (remove tokens and UseKeyring flags)
	cleanConfigBeforeSave(m.userConfig)

	data, err := json.MarshalIndent(m.userConfig, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal user config: %w", err)
	}

	slog.Debug("Saving user config", "userID", userID, "path", userConfigPath)
	return os.WriteFile(userConfigPath, data, 0600)
}

// GetCurrentOrgConfig returns the current organization configuration
func (m *Manager) GetCurrentOrgConfig() (*v1.OrgConfig, error) {
	if m.config.CurrentSelection == nil {
		return nil, fmt.Errorf("no current organization selected")
	}

	slog.Debug("GetCurrentOrgConfig",
		"url", m.config.CurrentSelection.URL,
		"org", m.config.CurrentSelection.Org,
		"hasUserConfig", m.userConfig != nil,
		"currentUser", m.config.CurrentUser)

	// FIRST: Check user config (if loaded)
	if m.userConfig != nil {
		if urlConfig, exists := m.userConfig.URLs[m.config.CurrentSelection.URL]; exists {
			slog.Debug("Found URL in user config", "url", m.config.CurrentSelection.URL, "orgs", len(urlConfig.Orgs))
			if orgConfig, exists := urlConfig.Orgs[m.config.CurrentSelection.Org]; exists {
				slog.Debug("Found org in user config", "org", m.config.CurrentSelection.Org)
				return orgConfig, nil
			}
		}
	}

	// THEN: Fall back to global config
	if urlConfig, exists := m.config.URLs[m.config.CurrentSelection.URL]; exists {
		slog.Debug("Found URL in global config", "url", m.config.CurrentSelection.URL, "orgs", len(urlConfig.Orgs))
		if orgConfig, exists := urlConfig.Orgs[m.config.CurrentSelection.Org]; exists {
			slog.Debug("Found org in global config", "org", m.config.CurrentSelection.Org)
			return orgConfig, nil
		}
	}

	return nil, fmt.Errorf("org %s not found under URL %s", m.config.CurrentSelection.Org, m.config.CurrentSelection.URL)
}

// GetCurrentOrgToken returns the token for the current organization
func (m *Manager) GetCurrentOrgToken() (string, error) {
	orgConfig, err := m.GetCurrentOrgConfig()
	if err != nil {
		return "", err
	}

	return m.getOrgToken(orgConfig)
}

// getOrgToken retrieves the token for an org from keyring
func (m *Manager) getOrgToken(org *v1.OrgConfig) (string, error) {
	slog.Debug("getOrgToken called",
		"org", org.Name,
		"keyringKey", org.KeyringKey)

	// Try user-scoped keyring first if user is active
	activeUser := m.GetActiveUser()
	if activeUser != nil {
		keyringService := fmt.Sprintf("%s:%s", KeyringService, activeUser.ID)
		slog.Debug("Attempting to get token from user-scoped keyring",
			"service", keyringService,
			"key", org.KeyringKey)
		token, err := keyring.Get(keyringService, org.KeyringKey)
		if err == nil && token != "" {
			slog.Debug("Successfully retrieved token from user-scoped keyring",
				"org", org.Name, "tokenLen", len(token))
			return token, nil
		}
		slog.Debug("Failed to get token from user-scoped keyring", "error", err)
	}

	// Fallback to legacy keyring format
	slog.Debug("Attempting to get token from legacy keyring",
		"service", KeyringService,
		"key", org.KeyringKey)
	token, err := keyring.Get(KeyringService, org.KeyringKey)
	if err == nil && token != "" {
		slog.Debug("Successfully retrieved token from legacy keyring",
			"org", org.Name, "tokenLen", len(token))
		return token, nil
	}
	slog.Debug("Failed to get token from legacy keyring", "error", err)

	slog.Debug("No token found for org", "org", org.Name)
	return "", fmt.Errorf("no token found for org %s", org.Name)
}

// setOrgToken stores the token for an org
func (m *Manager) setOrgToken(org *v1.OrgConfig, token string) error {
	if token == "" {
		return fmt.Errorf("cannot store empty token for organization %s", org.Name)
	}

	// Use user-scoped keyring if user is active, otherwise use legacy keyring
	service := KeyringService
	activeUser := m.GetActiveUser()
	if activeUser != nil {
		service = fmt.Sprintf("%s:%s", KeyringService, activeUser.ID)
		slog.Debug("Storing token in user-scoped keyring", "service", service, "key", org.KeyringKey)
	} else {
		slog.Debug("Storing token in legacy keyring", "service", service, "key", org.KeyringKey)
	}

	// Always store in keyring (with automatic fallback to file if needed)
	if err := keyring.Set(service, org.KeyringKey, token); err != nil {
		return fmt.Errorf("failed to store token in keyring: %w", err)
	}

	org.UseKeyring = true
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

	var urlConfig *v1.URLConfig

	// FIRST: Try to add to user config if user is active
	if m.userConfig != nil && m.config.CurrentUser != "" {
		// Ensure URL config exists in user's URLs
		if _, exists := m.userConfig.URLs[url]; !exists {
			m.userConfig.URLs[url] = &v1.URLConfig{
				URL:  url,
				Orgs: make(map[string]*v1.OrgConfig),
			}
		}
		urlConfig = m.userConfig.URLs[url]
	} else {
		// THEN: Fall back to global config
		if _, exists := m.config.URLs[url]; !exists {
			m.config.URLs[url] = &v1.URLConfig{
				URL:  url,
				Orgs: make(map[string]*v1.OrgConfig),
			}
		}
		urlConfig = m.config.URLs[url]
	}

	// Ensure org config exists
	orgConfig, orgExists := urlConfig.Orgs[orgName]
	if !orgExists {
		// New org - create keyring key
		orgConfig = &v1.OrgConfig{
			Name:       orgName,
			KeyringKey: buildKeyringKeyV1(url, orgName, ""),
			Sprites:    make(map[string]*v1.SpriteConfig),
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
	var urlConfig *v1.URLConfig
	var exists bool

	// FIRST: Try user config
	if m.userConfig != nil {
		urlConfig, exists = m.userConfig.URLs[url]
		if exists {
			if err := m.removeSpriteFromConfig(m.userConfig, urlConfig, url, orgName, spriteName); err != nil {
				return err
			}
			return m.Save()
		}
	}

	// THEN: Try global config
	urlConfig, exists = m.config.URLs[url]
	if !exists {
		return fmt.Errorf("URL %s not found", url)
	}

	return m.removeSpriteFromConfig(m.config, urlConfig, url, orgName, spriteName)
}

// removeSpriteFromConfig is a helper to remove a sprite from a config
func (m *Manager) removeSpriteFromConfig(cfg *v1.Config, urlConfig *v1.URLConfig, url, orgName, spriteName string) error {

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
			activeUser := m.GetActiveUser()
			if activeUser != nil {
				keyringService := fmt.Sprintf("%s:%s", KeyringService, activeUser.ID)
				_ = keyring.Delete(keyringService, orgConfig.KeyringKey)
			} else {
				_ = keyring.Delete(KeyringService, orgConfig.KeyringKey)
			}
		}
		delete(urlConfig.Orgs, orgName)
	}

	// If URL has no more orgs, remove it from the appropriate config
	if len(urlConfig.Orgs) == 0 {
		delete(cfg.URLs, url)
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

// GetAllSprites returns all sprites organized by URL and org for the active user
func (m *Manager) GetAllSprites() map[string]*v1.URLConfig {
	// FIRST: Return user config if loaded
	if m.userConfig != nil {
		return m.userConfig.URLs
	}

	// THEN: Fall back to global config
	return m.config.URLs
}

// FindSprite finds a sprite by name, handling conflicts
func (m *Manager) FindSprite(spriteName string) (*v1.SpriteConfig, string, string, string, error) {
	var foundSprites []struct {
		sprite *v1.SpriteConfig
		url    string
		org    string
	}

	// FIRST: Search user config (if loaded)
	if m.userConfig != nil {
		for url, urlConfig := range m.userConfig.URLs {
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
	}

	// THEN: Search global config
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

	// Add URLs from active user's URLs
	activeUser := m.GetActiveUser()
	if activeUser != nil {
		for url := range m.userConfig.URLs {
			urlSet[url] = true
		}
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

// User management methods

// AddUser adds a new user to the config
func (m *Manager) AddUser(userID, email string) error {
	// Check if user already exists
	for _, u := range m.config.Users {
		if u.ID == userID {
			// User already exists, just load their config
			return m.loadUserConfig(userID)
		}
	}

	// Get paths for user's config and token files
	userConfigPath, err := getUserConfigPath(userID)
	if err != nil {
		return fmt.Errorf("failed to get user config path: %w", err)
	}

	// Import from client/fly package to get token path
	tokenPath := filepath.Join(filepath.Dir(userConfigPath), fmt.Sprintf("%s-%s.token.enc", userID, hashUserID(userID)))

	// Add user to list
	userInfo := &v1.UserInfo{
		ID:         userID,
		Email:      email,
		ConfigPath: userConfigPath,
		TokenPath:  tokenPath,
	}
	m.config.Users = append(m.config.Users, userInfo)

	// Set as current user if no current user is set
	if m.config.CurrentUser == "" {
		m.config.CurrentUser = userID
	}

	// Load/create user config
	if err := m.loadUserConfig(userID); err != nil {
		return fmt.Errorf("failed to load user config: %w", err)
	}

	return m.Save()
}

// GetUser returns a user by ID
func (m *Manager) GetUser(userID string) *v1.UserInfo {
	for _, u := range m.config.Users {
		slog.Debug("GetUser", "userID", u.ID, "userConfigPath", u.ConfigPath, "userTokenPath", u.TokenPath)
		if u.ID == userID {
			return u
		}
	}
	return nil
}

// GetActiveUser returns the currently active user
func (m *Manager) GetActiveUser() *v1.UserInfo {
	slog.Debug("GetActiveUser",
		"activeUserID", m.config.CurrentUser,
		"totalUsers", len(m.config.Users))

	if m.config.CurrentUser == "" {
		slog.Debug("No active user ID set")
		return nil
	}

	user := m.GetUser(m.config.CurrentUser)
	if user == nil {
		slog.Debug("Active user not found in users list", "activeUserID", m.config.CurrentUser)
	} else {
		slog.Debug("Active user found",
			"userID", user.ID,
			"email", user.Email,
			"hasUserConfig", m.userConfig != nil)
	}

	return user
}

// SetActiveUser sets the active user
func (m *Manager) SetActiveUser(userID string) error {
	// Check if user exists
	if m.GetUser(userID) == nil {
		return fmt.Errorf("user %s not found", userID)
	}

	m.config.CurrentUser = userID

	// Load the user's config
	if err := m.loadUserConfig(userID); err != nil {
		return fmt.Errorf("failed to load user config: %w", err)
	}

	return m.Save()
}

// RemoveUser removes a user and all their tokens from keyring
func (m *Manager) RemoveUser(userID string) error {
	user := m.GetUser(userID)
	if user == nil {
		return fmt.Errorf("user %s not found", userID)
	}

	// Load user config to get their orgs
	if err := m.loadUserConfig(userID); err == nil && m.userConfig != nil {
		// Remove all tokens from user's keyring service
		keyringService := fmt.Sprintf("%s:%s", KeyringService, userID)
		for _, urlConfig := range m.userConfig.URLs {
			for orgName := range urlConfig.Orgs {
				keyringKey := fmt.Sprintf("sprites:org:%s", orgName)
				_ = keyring.Delete(keyringService, keyringKey)
			}
		}
	}

	// Delete user config file
	if userConfigPath, err := getUserConfigPath(userID); err == nil {
		_ = os.Remove(userConfigPath)
	}

	// Remove user from list
	newUsers := make([]*v1.UserInfo, 0)
	for _, u := range m.config.Users {
		if u.ID != userID {
			newUsers = append(newUsers, u)
		}
	}
	m.config.Users = newUsers

	// Clear current user if it was this user
	if m.config.CurrentUser == userID {
		m.config.CurrentUser = ""
		m.userConfig = nil
		m.currentUserID = ""
	}

	return m.Save()
}

// GetAllUsers returns all configured users as a map
func (m *Manager) GetAllUsers() map[string]*v1.UserInfo {
	users := make(map[string]*v1.UserInfo)
	for _, u := range m.config.Users {
		users[u.ID] = u
	}
	return users
}

// BuildUserKeyringService creates a user-scoped keyring service name
func BuildUserKeyringService(userID string) string {
	return fmt.Sprintf("%s:%s", KeyringService, userID)
}
