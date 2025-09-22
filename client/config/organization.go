package config

import (
	"fmt"
	"log/slog"
	"os"

	v1 "github.com/superfly/sprite-env/client/config/v1"
	"github.com/zalando/go-keyring"
)

// Organization represents a simplified view of org configuration for client commands
type Organization struct {
	Name        string
	URL         string
	Token       string // Only populated when explicitly retrieved
	UseKeyring  bool
	manager     *Manager // Reference to manager for operations
	keychainKey string
}

// GetToken retrieves the token for this organization
func (o *Organization) GetToken() (string, error) {
	return o.GetTokenWithKeyringDisabled(false)
}

// GetTokenWithKeyringDisabled retrieves the token with optional keyring bypass
func (o *Organization) GetTokenWithKeyringDisabled(disableKeyring bool) (string, error) {
	// If token is already populated (e.g., from env vars), return it
	if o.Token != "" {
		return o.Token, nil
	}

	// If we have a manager and keychain key, try to get from storage
	if o.manager != nil && o.keychainKey != "" {
		if !disableKeyring && o.UseKeyring {
			// Try keyring first
			token, err := keyring.Get(KeyringService, o.keychainKey)
			if err == nil && token != "" {
				return token, nil
			}
		}
	}

	// Check for SPRITE_TOKEN environment variable as fallback
	if envToken := os.Getenv("SPRITE_TOKEN"); envToken != "" {
		return envToken, nil
	}

	return "", fmt.Errorf("no token found for organization %s", o.Name)
}

// GetOrgs returns all organizations as a flattened map for backward compatibility
func (m *Manager) GetOrgs() map[string]*Organization {
	orgs := make(map[string]*Organization)

	// Flatten the hierarchical structure
	for url, urlConfig := range m.config.URLs {
		for _, orgConfig := range urlConfig.Orgs {
			org := &Organization{
				Name:        orgConfig.Name,
				URL:         url,
				UseKeyring:  orgConfig.UseKeyring,
				manager:     m,
				keychainKey: orgConfig.KeychainKey,
			}

			// Pre-populate token if not using keyring
			if !orgConfig.UseKeyring && orgConfig.Token != "" {
				org.Token = orgConfig.Token
			}

			orgs[orgConfig.Name] = org
		}
	}

	return orgs
}

// GetCurrentOrg returns the currently selected organization
func (m *Manager) GetCurrentOrg() *Organization {
	if m.config.CurrentSelection == nil {
		return nil
	}

	// Get the org config
	urlConfig, exists := m.config.URLs[m.config.CurrentSelection.URL]
	if !exists {
		return nil
	}

	orgConfig, exists := urlConfig.Orgs[m.config.CurrentSelection.Org]
	if !exists {
		return nil
	}

	org := &Organization{
		Name:        orgConfig.Name,
		URL:         m.config.CurrentSelection.URL,
		UseKeyring:  orgConfig.UseKeyring,
		manager:     m,
		keychainKey: orgConfig.KeychainKey,
	}

	// Pre-populate token if not using keyring
	if !orgConfig.UseKeyring && orgConfig.Token != "" {
		org.Token = orgConfig.Token
	}

	return org
}

// SetCurrentOrg sets the current organization by name
func (m *Manager) SetCurrentOrg(orgName string) error {
	// Find any org that matches this name across all URLs
	for url, urlConfig := range m.config.URLs {
		if _, exists := urlConfig.Orgs[orgName]; exists {
			// Found the org, set it as current
			m.config.CurrentSelection = &v1.CurrentSelection{
				URL: url,
				Org: orgName,
			}
			return m.Save()
		}
	}

	return fmt.Errorf("organization %s not found", orgName)
}

// AddOrg adds an organization (for backward compatibility)
// This creates both an org and a sprite with the same name
func (m *Manager) AddOrg(name, token, url string) error {
	// Use the org name as both org and sprite name for backward compatibility
	return m.AddSprite(url, name, name, token)
}

// RemoveOrg removes an organization by name and URL
func (m *Manager) RemoveOrg(name string) error {
	// Find and remove all sprites with this org name
	var removed bool

	for url, urlConfig := range m.config.URLs {
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

// AddOrgMetadataOnly adds an organization to config without touching any existing token in keyring
// This is used during org discovery to add orgs that have tokens in keyring but not in config
func (m *Manager) AddOrgMetadataOnly(name, url string) error {
	// Check if org already exists
	if urlConfig, exists := m.config.URLs[url]; exists {
		if _, exists := urlConfig.Orgs[name]; exists {
			// Already exists, nothing to do
			return nil
		}
	}

	// Ensure URL config exists
	if _, exists := m.config.URLs[url]; !exists {
		m.config.URLs[url] = &v1.URLConfig{
			URL:  url,
			Orgs: make(map[string]*v1.OrgConfig),
		}
	}

	// Add org without token
	orgConfig := &v1.OrgConfig{
		Name:        name,
		KeychainKey: name, // Use legacy keychain key format for discovered orgs
		UseKeyring:  true,
		Sprites:     make(map[string]*v1.SpriteConfig),
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
			// Look for the org under this specific URL
			slog.Debug("FindOrgWithAlias: looking for org in URL config", "url", url, "orgName", orgName, "availableURLs", len(m.config.URLs))
			if urlConfig, urlExists := m.config.URLs[url]; urlExists {
				slog.Debug("FindOrgWithAlias: found URL config", "url", url, "orgsCount", len(urlConfig.Orgs))
				if orgConfig, orgExists := urlConfig.Orgs[orgName]; orgExists {
					org := &Organization{
						Name:        orgConfig.Name,
						URL:         url,
						UseKeyring:  orgConfig.UseKeyring,
						manager:     m,
						keychainKey: orgConfig.KeychainKey,
					}
					// Only set token if not using keyring
					if !orgConfig.UseKeyring && orgConfig.Token != "" {
						org.Token = orgConfig.Token
					}
					slog.Debug("FindOrgWithAlias: returning org", "name", org.Name, "url", org.URL, "alias", alias)
					return org, url, nil
				}
			}
			return nil, "", fmt.Errorf("organization %s not found under URL %s (alias: %s)", orgName, url, alias)
		}
		// Unknown alias - will need to prompt user
		return nil, "", fmt.Errorf("unknown alias: %s", alias)
	}

	// No alias - search all URLs for this org
	var foundOrgs []struct {
		org *Organization
		url string
	}

	for url, urlConfig := range m.config.URLs {
		if orgConfig, exists := urlConfig.Orgs[orgName]; exists {
			org := &Organization{
				Name:        orgConfig.Name,
				URL:         url,
				UseKeyring:  orgConfig.UseKeyring,
				manager:     m,
				keychainKey: orgConfig.KeychainKey,
			}
			// Only set token if not using keyring
			if !orgConfig.UseKeyring && orgConfig.Token != "" {
				org.Token = orgConfig.Token
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
