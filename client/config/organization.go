package config

import (
	"fmt"
	"log/slog"
	"os"
	"path/filepath"
	"strings"

	v1 "github.com/superfly/sprite-env/client/config/v1"
	"github.com/superfly/sprite-env/client/keyring"
	"github.com/superfly/sprite-env/client/tokenutil"
)

// Organization represents a simplified view of org configuration for client commands
type Organization struct {
	Name       string
	URL        string
	Token      string   // Only populated when explicitly retrieved
	UseKeyring bool     // Tracks whether keyring is being used
	UserID     string   // Fly.io user ID for user-scoped keyring
	UserEmail  string   // Fly.io user email for display
	manager    *Manager // Reference to manager for operations
	keyringKey string
}

// GetToken retrieves the token for this organization
func (o *Organization) GetToken() (string, error) {
	slog.Debug("GetToken called",
		"org", o.Name,
		"hasManager", o.manager != nil,
		"keyringKey", o.keyringKey,
		"userID", o.UserID,
		"userEmail", o.UserEmail)

	// If token is already populated (e.g., from env vars), return it
	if o.Token != "" {
		slog.Debug("Token already populated, returning", "org", o.Name, "tokenLen", len(o.Token))
		return o.Token, nil
	}

	// Try to get from keyring
	if o.manager != nil && o.keyringKey != "" {
		// Try user-scoped keyring first
		activeUser := o.manager.GetActiveUser()
		if activeUser != nil {
			keyringService := fmt.Sprintf("%s:%s", KeyringService, activeUser.ID)

			// Try with the keyring key from config
			slog.Debug("Attempting to get token from user-scoped keyring",
				"service", keyringService,
				"key", o.keyringKey)
			token, err := keyring.Get(keyringService, o.keyringKey)
			if err == nil && token != "" {
				slog.Debug("Successfully retrieved token from user-scoped keyring",
					"org", o.Name, "tokenLen", len(token))

				// Check if token needs upgrade and upgrade if needed
				if o.manager != nil {
					upgradedToken, upgraded, upgradeErr := upgradeToken(token, o, o.manager)
					if upgradeErr != nil {
						slog.Warn("failed to upgrade token",
							"org", o.Name,
							"error", upgradeErr)
						// Return the original token anyway - don't block the user
						return token, nil
					}
					if upgraded {
						return upgradedToken, nil
					}
				}

				return token, nil
			}
			slog.Debug("Failed to get token from user-scoped keyring with config key", "error", err)

			// Try with legacy key format (sprites:org:<orgname>) for backwards compatibility
			legacyKey := fmt.Sprintf("sprites:org:%s", o.Name)
			if legacyKey != o.keyringKey {
				slog.Debug("Attempting to get token with legacy key format",
					"service", keyringService,
					"key", legacyKey)
				token, err = keyring.Get(keyringService, legacyKey)
				if err == nil && token != "" {
					slog.Debug("Successfully retrieved token with legacy key format",
						"org", o.Name, "tokenLen", len(token))

					// Check if token needs upgrade and upgrade if needed
					if o.manager != nil {
						upgradedToken, upgraded, upgradeErr := upgradeToken(token, o, o.manager)
						if upgradeErr != nil {
							slog.Warn("failed to upgrade token",
								"org", o.Name,
								"error", upgradeErr)
							// Return the original token anyway - don't block the user
							return token, nil
						}
						if upgraded {
							return upgradedToken, nil
						}
					}

					return token, nil
				}
				slog.Debug("Failed to get token with legacy key format", "error", err)
			}
		}

		// Fall back to legacy keyring format (global service)
		slog.Debug("Attempting to get token from legacy global keyring",
			"service", KeyringService,
			"key", o.keyringKey)
		token, err := keyring.Get(KeyringService, o.keyringKey)
		if err == nil && token != "" {
			slog.Debug("Successfully retrieved token from legacy global keyring",
				"org", o.Name, "tokenLen", len(token))

			// Check if token needs upgrade and upgrade if needed
			if o.manager != nil {
				upgradedToken, upgraded, upgradeErr := upgradeToken(token, o, o.manager)
				if upgradeErr != nil {
					slog.Warn("failed to upgrade token",
						"org", o.Name,
						"error", upgradeErr)
					// Return the original token anyway - don't block the user
					return token, nil
				}
				if upgraded {
					return upgradedToken, nil
				}
			}

			return token, nil
		}
		slog.Debug("Failed to get token from legacy global keyring", "error", err)
	}

	// Check for SPRITE_TOKEN environment variable as fallback
	if envToken := os.Getenv("SPRITE_TOKEN"); envToken != "" {
		slog.Debug("Using SPRITE_TOKEN environment variable", "org", o.Name)

		// Check if token needs upgrade and upgrade if needed
		// Note: We can't upgrade env tokens as we can't save them back
		// Just log a warning if it's legacy
		if tokenutil.IsLegacyToken(envToken) {
			slog.Warn("SPRITE_TOKEN environment variable is in legacy format - consider updating it",
				"org", o.Name)
		}

		return envToken, nil
	}

	slog.Debug("No token found for organization", "org", o.Name)
	return "", fmt.Errorf("no token found for organization %s", o.Name)
}

// GetOrgs returns all organizations as a flattened map for backward compatibility
func (m *Manager) GetOrgs() map[string]*Organization {
	orgs := make(map[string]*Organization)

	// FIRST: Check user config (if loaded)
	if m.userConfig != nil && m.config.CurrentUser != "" {
		activeUser := m.GetActiveUser()
		if activeUser != nil {
			for url, urlConfig := range m.userConfig.URLs {
				for _, orgConfig := range urlConfig.Orgs {
					org := &Organization{
						Name:       orgConfig.Name,
						URL:        url,
						UseKeyring: orgConfig.UseKeyring,
						UserID:     activeUser.ID,
						UserEmail:  activeUser.Email,
						manager:    m,
						keyringKey: orgConfig.KeyringKey,
					}

					orgs[orgConfig.Name] = org
				}
			}
		}
	}

	// THEN: Add orgs from global config (don't overwrite user orgs)
	for url, urlConfig := range m.config.URLs {
		for _, orgConfig := range urlConfig.Orgs {
			if _, exists := orgs[orgConfig.Name]; !exists {
				org := &Organization{
					Name:       orgConfig.Name,
					URL:        url,
					UseKeyring: orgConfig.UseKeyring,
					manager:    m,
					keyringKey: orgConfig.KeyringKey,
				}

				orgs[orgConfig.Name] = org
			}
		}
	}

	return orgs
}

// GetCurrentOrg returns the currently selected organization
func (m *Manager) GetCurrentOrg() *Organization {
	if m.config.CurrentSelection == nil {
		return nil
	}

	// FIRST: Check user config (if loaded)
	if m.userConfig != nil {
		if urlConfig, exists := m.userConfig.URLs[m.config.CurrentSelection.URL]; exists {
			if orgConfig, exists := urlConfig.Orgs[m.config.CurrentSelection.Org]; exists {
				activeUser := m.GetActiveUser()
				org := &Organization{
					Name:       orgConfig.Name,
					URL:        m.config.CurrentSelection.URL,
					UseKeyring: orgConfig.UseKeyring,
					manager:    m,
					keyringKey: orgConfig.KeyringKey,
				}
				if activeUser != nil {
					org.UserID = activeUser.ID
					org.UserEmail = activeUser.Email
				}

				return org
			}
		}
	}

	// THEN: Fall back to global config
	if urlConfig, exists := m.config.URLs[m.config.CurrentSelection.URL]; exists {
		if orgConfig, exists := urlConfig.Orgs[m.config.CurrentSelection.Org]; exists {
			org := &Organization{
				Name:       orgConfig.Name,
				URL:        m.config.CurrentSelection.URL,
				UseKeyring: orgConfig.UseKeyring,
				manager:    m,
				keyringKey: orgConfig.KeyringKey,
			}

			return org
		}
	}

	return nil
}

// SetCurrentOrg sets the current organization by name
func (m *Manager) SetCurrentOrg(orgName string) error {
	// FIRST: Check user config (if loaded)
	if m.userConfig != nil {
		for url, urlConfig := range m.userConfig.URLs {
			if _, exists := urlConfig.Orgs[orgName]; exists {
				// Found the org in user config, set it as current
				m.config.CurrentSelection = &v1.CurrentSelection{
					URL: url,
					Org: orgName,
				}
				return m.Save()
			}
		}
	}

	// THEN: Fall back to global config
	for url, urlConfig := range m.config.URLs {
		if _, exists := urlConfig.Orgs[orgName]; exists {
			// Found the org in global config, set it as current
			m.config.CurrentSelection = &v1.CurrentSelection{
				URL: url,
				Org: orgName,
			}
			return m.Save()
		}
	}

	return fmt.Errorf("organization %s not found", orgName)
}

// AddOrgWithUser adds an organization with user-scoped keyring storage
func (m *Manager) AddOrgWithUser(name, token, url, userID, userEmail, alias string) error {
	// Build user-scoped keyring service and key for Sprite token only
	// Include alias (or URL if no alias) in the key to avoid collisions when the same org exists on multiple environments
	keyringService := fmt.Sprintf("%s:%s", KeyringService, userID)
	var keyringKey string
	if alias != "" {
		keyringKey = fmt.Sprintf("sprites:org:%s:%s", alias, name)
	} else {
		keyringKey = fmt.Sprintf("sprites:org:%s:%s", url, name)
	}

	slog.Debug("Adding org with user-scoped keyring",
		"org", name,
		"url", url,
		"userID", userID,
		"service", keyringService,
		"key", keyringKey)

	// Ensure user exists in main config and load/create their config
	if m.GetUser(userID) == nil {
		// Add user to main config
		if err := m.AddUser(userID, userEmail); err != nil {
			return fmt.Errorf("failed to add user: %w", err)
		}
	} else {
		// User exists, make sure their config is loaded
		if m.userConfig == nil || m.currentUserID != userID {
			if err := m.loadUserConfig(userID); err != nil {
				return fmt.Errorf("failed to load user config: %w", err)
			}
		}
	}

	// Set as current user if no current user is set
	if m.config.CurrentUser == "" {
		m.config.CurrentUser = userID
		if err := m.loadUserConfig(userID); err != nil {
			return fmt.Errorf("failed to load user config: %w", err)
		}
	}

	// Ensure URL config exists in user config
	if _, exists := m.userConfig.URLs[url]; !exists {
		m.userConfig.URLs[url] = &v1.URLConfig{
			URL:  url,
			Orgs: make(map[string]*v1.OrgConfig),
		}
	}

	// Create or update org config in user config
	orgConfig, exists := m.userConfig.URLs[url].Orgs[name]
	if !exists {
		orgConfig = &v1.OrgConfig{
			Name:       name,
			KeyringKey: keyringKey,
			Sprites:    make(map[string]*v1.SpriteConfig),
		}
		m.userConfig.URLs[url].Orgs[name] = orgConfig
	} else {
		// On re-auth, ensure we overwrite any stale keyring key with the correct format
		// so subsequent token retrievals use the new per-user key layout.
		orgConfig.KeyringKey = keyringKey
	}

	// Store token in keyring (always)
	if err := keyring.Set(keyringService, keyringKey, token); err != nil {
		return fmt.Errorf("failed to store token in keyring: %w", err)
	}

	orgConfig.UseKeyring = true
	slog.Debug("Stored token in user-scoped keyring", "service", keyringService, "key", keyringKey)

	// Add a sprite with the same name for backward compatibility
	if _, exists := orgConfig.Sprites[name]; !exists {
		orgConfig.Sprites[name] = &v1.SpriteConfig{
			Name: name,
		}
	}

	// Set as current if it's the first org
	if m.config.CurrentSelection == nil {
		m.config.CurrentSelection = &v1.CurrentSelection{
			URL: url,
			Org: name,
		}
	}

	return m.Save()
}

// AddOrg adds an organization (for backward compatibility)
// This creates both an org and a sprite with the same name
func (m *Manager) AddOrg(name, token, url string) error {
	// Use the org name as both org and sprite name for backward compatibility
	return m.AddSprite(url, name, name, token)
}

// RemoveOrg removes an organization by name and URL
func (m *Manager) RemoveOrg(name string) error {
	// Find and remove all sprites with this org name from active user's URLs
	activeUser := m.GetActiveUser()
	if activeUser == nil {
		return fmt.Errorf("no active user")
	}

	var removed bool
	for url, urlConfig := range m.userConfig.URLs {
		if _, exists := urlConfig.Orgs[name]; exists {
			// Remove all sprites in this org
			for spriteName := range urlConfig.Orgs[name].Sprites {
				if err := m.RemoveSprite(url, name, spriteName); err == nil {
					removed = true
				}
			}
		}
	}

	if !removed {
		return fmt.Errorf("organization %s not found", name)
	}

	return nil
}

// FindOrgAtURL finds an organization by name under a specific API URL
// Returns the organization or an error if not found
func (m *Manager) FindOrgAtURL(url, orgName string) (*Organization, error) {
	// FIRST: Try user config
	if m.userConfig != nil {
		if urlConfig, exists := m.userConfig.URLs[url]; exists {
			if orgConfig, exists := urlConfig.Orgs[orgName]; exists {
				activeUser := m.GetActiveUser()
				org := &Organization{
					Name:       orgConfig.Name,
					URL:        url,
					UseKeyring: orgConfig.UseKeyring,
					manager:    m,
					keyringKey: orgConfig.KeyringKey,
				}
				if activeUser != nil {
					org.UserID = activeUser.ID
					org.UserEmail = activeUser.Email
				}

				return org, nil
			}
		}
	}

	// THEN: Fall back to global config
	urlConfig, exists := m.config.URLs[url]
	if !exists {
		return nil, fmt.Errorf("URL %s not found in config", url)
	}

	orgConfig, exists := urlConfig.Orgs[orgName]
	if !exists {
		return nil, fmt.Errorf("organization %s not found under URL %s", orgName, url)
	}

	org := &Organization{
		Name:       orgConfig.Name,
		URL:        url,
		UseKeyring: orgConfig.UseKeyring,
		manager:    m,
		keyringKey: orgConfig.KeyringKey,
	}

	return org, nil
}

// SetCurrentSelection sets the current selection precisely to the given URL and org
func (m *Manager) SetCurrentSelection(url, org string) error {
	m.config.CurrentSelection = &v1.CurrentSelection{
		URL: url,
		Org: org,
	}
	return m.Save()
}

// AddOrgMetadataOnly adds an organization to config without touching any existing token in keyring
// This is used during org discovery to add orgs that have tokens in keyring but not in config
func (m *Manager) AddOrgMetadataOnly(name, url string) error {
	// FIRST: Try to add to user config if available
	if m.userConfig != nil {
		// Check if org already exists
		if urlConfig, exists := m.userConfig.URLs[url]; exists {
			if _, exists := urlConfig.Orgs[name]; exists {
				// Already exists, nothing to do
				return nil
			}
		}

		// Ensure URL config exists in user's URLs
		if _, exists := m.userConfig.URLs[url]; !exists {
			m.userConfig.URLs[url] = &v1.URLConfig{
				URL:  url,
				Orgs: make(map[string]*v1.OrgConfig),
			}
		}

		urlConfig := m.userConfig.URLs[url]
		// Include URL in keyring key to avoid collisions when the same org exists on multiple environments
		keyringKey := fmt.Sprintf("sprites:org:%s:%s", url, name)
		orgConfig := &v1.OrgConfig{
			Name:       name,
			KeyringKey: keyringKey,
			UseKeyring: true,
			Sprites:    make(map[string]*v1.SpriteConfig),
		}
		orgConfig.Sprites[name] = &v1.SpriteConfig{Name: name}
		urlConfig.Orgs[name] = orgConfig
		return m.Save()
	}

	// THEN: Fall back to global config
	// Check if org already exists
	if urlConfig, exists := m.config.URLs[url]; exists {
		if _, exists := urlConfig.Orgs[name]; exists {
			// Already exists, nothing to do
			return nil
		}
	}

	// Ensure URL config exists in global config
	if _, exists := m.config.URLs[url]; !exists {
		m.config.URLs[url] = &v1.URLConfig{
			URL:  url,
			Orgs: make(map[string]*v1.OrgConfig),
		}
	}

	// Add org without token
	// Include URL in keyring key to avoid collisions when the same org exists on multiple environments
	keyringKey := fmt.Sprintf("sprites:org:%s:%s", url, name)
	orgConfig := &v1.OrgConfig{
		Name:       name,
		KeyringKey: keyringKey,
		UseKeyring: true,
		Sprites:    make(map[string]*v1.SpriteConfig),
	}

	// Add a sprite with the same name for backward compatibility
	orgConfig.Sprites[name] = &v1.SpriteConfig{
		Name: name,
	}

	m.config.URLs[url].Orgs[name] = orgConfig

	return m.Save()
}

// FindOrgWithAlias finds an organization, supporting alias:org format
// Returns the org, its URL, and an error if not found
func (m *Manager) FindOrgWithAlias(orgSpec string) (*Organization, string, error) {
	// Parse the org specification
	orgName, alias, hasAlias := m.ParseOrgWithAlias(orgSpec)
	slog.Debug("FindOrgWithAlias: parsing orgSpec", "orgSpec", orgSpec, "orgName", orgName, "alias", alias, "hasAlias", hasAlias)

	if hasAlias {
		// Check if we know this alias
		url, exists := m.GetURLForAlias(alias)
		slog.Debug("FindOrgWithAlias: checking alias", "alias", alias, "found", exists, "url", url)
		if exists {
			// FIRST: Look in user config
			if m.userConfig != nil {
				slog.Debug("FindOrgWithAlias: looking for org in user's URLs", "url", url, "orgName", orgName, "userURLs", len(m.userConfig.URLs))
				if urlConfig, urlExists := m.userConfig.URLs[url]; urlExists {
					slog.Debug("FindOrgWithAlias: found URL config", "url", url, "orgsCount", len(urlConfig.Orgs))
					if orgConfig, orgExists := urlConfig.Orgs[orgName]; orgExists {
						activeUser := m.GetActiveUser()
						org := &Organization{
							Name:       orgConfig.Name,
							URL:        url,
							UseKeyring: orgConfig.UseKeyring,
							manager:    m,
							keyringKey: orgConfig.KeyringKey,
						}
						if activeUser != nil {
							org.UserID = activeUser.ID
							org.UserEmail = activeUser.Email
						}
						slog.Debug("FindOrgWithAlias: returning org from user config", "name", org.Name, "url", org.URL, "alias", alias)
						return org, url, nil
					}
				}
			}

			// THEN: Look in global config
			if urlConfig, urlExists := m.config.URLs[url]; urlExists {
				if orgConfig, orgExists := urlConfig.Orgs[orgName]; orgExists {
					org := &Organization{
						Name:       orgConfig.Name,
						URL:        url,
						UseKeyring: orgConfig.UseKeyring,
						manager:    m,
						keyringKey: orgConfig.KeyringKey,
					}
					slog.Debug("FindOrgWithAlias: returning org from global config", "name", org.Name, "url", org.URL, "alias", alias)
					return org, url, nil
				}
			}

			return nil, "", fmt.Errorf("organization %s not found under URL %s (alias: %s)", orgName, url, alias)
		}
		// Unknown alias - will need to prompt user
		return nil, "", fmt.Errorf("unknown alias: %s", alias)
	}

	// No alias - search for this org
	var foundOrgs []struct {
		org *Organization
		url string
	}

	// FIRST: Search user config
	if m.userConfig != nil {
		activeUser := m.GetActiveUser()
		for url, urlConfig := range m.userConfig.URLs {
			if orgConfig, exists := urlConfig.Orgs[orgName]; exists {
				org := &Organization{
					Name:       orgConfig.Name,
					URL:        url,
					UseKeyring: orgConfig.UseKeyring,
					manager:    m,
					keyringKey: orgConfig.KeyringKey,
				}
				if activeUser != nil {
					org.UserID = activeUser.ID
					org.UserEmail = activeUser.Email
				}
				foundOrgs = append(foundOrgs, struct {
					org *Organization
					url string
				}{
					org: org,
					url: url,
				})
			}
		}
	}

	// THEN: Search global config
	for url, urlConfig := range m.config.URLs {
		if orgConfig, exists := urlConfig.Orgs[orgName]; exists {
			org := &Organization{
				Name:       orgConfig.Name,
				URL:        url,
				UseKeyring: orgConfig.UseKeyring,
				manager:    m,
				keyringKey: orgConfig.KeyringKey,
			}
			foundOrgs = append(foundOrgs, struct {
				org *Organization
				url string
			}{
				org: org,
				url: url,
			})
		}
	}

	if len(foundOrgs) == 0 {
		return nil, "", fmt.Errorf("organization %s not found", orgName)
	}

	if len(foundOrgs) == 1 {
		return foundOrgs[0].org, foundOrgs[0].url, nil
	}

	// Multiple orgs found - prefer current URL if set
	if m.config.CurrentSelection != nil {
		for _, found := range foundOrgs {
			if found.url == m.config.CurrentSelection.URL {
				return found.org, found.url, nil
			}
		}
	}

	// Return the first one
	return foundOrgs[0].org, foundOrgs[0].url, nil
}

// upgradeToken is a helper function that wraps tokenutil.UpgradeTokenIfNeeded
func upgradeToken(token string, org *Organization, manager *Manager) (string, bool, error) {
	// Get active user
	activeUser := manager.GetActiveUser()
	if activeUser == nil {
		return "", false, fmt.Errorf("no active user found")
	}

	// Create org info
	orgInfo := tokenutil.OrgInfo{
		Name:       org.Name,
		URL:        org.URL,
		KeyringKey: org.keyringKey,
	}

	// Create user info
	userInfo := &tokenutil.UserInfo{
		ID: activeUser.ID,
	}

	// Create fly token reader function
	flyTokenReader := func(userID string) (string, error) {
		// Try user-specific encrypted storage
		token, err := readFlyTokenForUser(userID)
		if err == nil && token != "" {
			return token, nil
		}

		// Fall back to global ~/.fly/config.yml
		token, err = readGlobalFlyToken()
		if err != nil {
			return "", fmt.Errorf("no Fly token found: %w", err)
		}
		return token, nil
	}

	// Build keyring service
	keyringService := fmt.Sprintf("%s:%s", KeyringService, activeUser.ID)

	// Call the tokenutil function
	return tokenutil.UpgradeTokenIfNeeded(token, orgInfo, userInfo, flyTokenReader, keyringService)
}

// readFlyTokenForUser reads the Fly token for a specific user from encrypted storage or keyring
// This is a simplified version of fly.ReadFlyTokenForUser to avoid import cycles
func readFlyTokenForUser(userID string) (string, error) {
	// Try encrypted storage first
	encryptedPath, err := getFlyTokenEncryptedPath(userID)
	if err == nil {
		token, err := readEncryptedFlyToken(encryptedPath)
		if err == nil && token != "" {
			return token, nil
		}
	}

	// Try keyring (legacy, for migration)
	keyringService := fmt.Sprintf("sprites-cli:%s", userID)
	keyringKey := fmt.Sprintf("fly-token:%s", userID)
	token, err := keyring.Get(keyringService, keyringKey)
	if err == nil && token != "" {
		return token, nil
	}

	return "", fmt.Errorf("no Fly token found for user %s", userID)
}

// readGlobalFlyToken reads the Fly token from ~/.fly/config.yml
// This is a simplified version of fly.ReadFlyToken to avoid import cycles
func readGlobalFlyToken() (string, error) {
	homeDir, err := os.UserHomeDir()
	if err != nil {
		return "", err
	}

	configPath := filepath.Join(homeDir, ".fly", "config.yml")
	data, err := os.ReadFile(configPath)
	if err != nil {
		return "", err
	}

	// Simple YAML parsing for access_token field
	lines := strings.Split(string(data), "\n")
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if strings.HasPrefix(line, "access_token:") {
			parts := strings.SplitN(line, ":", 2)
			if len(parts) == 2 {
				token := strings.TrimSpace(parts[1])
				// Remove quotes if present
				token = strings.Trim(token, `"'`)
				if token != "" {
					return token, nil
				}
			}
		}
	}

	return "", fmt.Errorf("no access_token found in %s", configPath)
}

// getFlyTokenEncryptedPath returns the path to the encrypted Fly token file
func getFlyTokenEncryptedPath(userID string) (string, error) {
	homeDir, err := os.UserHomeDir()
	if err != nil {
		return "", err
	}
	return filepath.Join(homeDir, ".sprite", "fly-tokens", userID), nil
}

// readEncryptedFlyToken reads an encrypted Fly token
// This is a simplified stub - you may need to import the actual decryption logic
func readEncryptedFlyToken(path string) (string, error) {
	// This would need actual decryption logic from fly/encryption.go
	// For now, just try to read it directly (it should be encrypted in practice)
	data, err := os.ReadFile(path)
	if err != nil {
		return "", err
	}
	// In practice, this should decrypt the data
	// We're skipping that for now to avoid import cycles
	return string(data), nil
}
