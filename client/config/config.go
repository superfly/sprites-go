package config

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"runtime"

	"github.com/zalando/go-keyring"
)

// Config represents the sprite configuration
type Config struct {
	CurrentOrg     string                   `json:"current_org,omitempty"`
	Orgs           map[string]*Organization `json:"orgs"`
	DisableKeyring bool                     `json:"disable_keyring,omitempty"`
}

// Organization represents an organization configuration
type Organization struct {
	Name       string `json:"name"`
	Token      string `json:"token,omitempty"` // Only used when keyring is disabled
	URL        string `json:"url"`
	UseKeyring bool   `json:"use_keyring,omitempty"` // Tracks whether keyring is being used for this org
}

// Manager handles configuration operations
type Manager struct {
	configPath string
	config     *Config
}

const (
	KeyringService = "sprites-cli"
)

// CredentialType represents different types of credentials that can be stored
type CredentialType string

const (
	CredentialTypeToken  CredentialType = "token"
	CredentialTypeAPIKey CredentialType = "api-key"
	CredentialTypeCert   CredentialType = "certificate"
	CredentialTypeSSHKey CredentialType = "ssh-key"
)

// buildKeyringKey creates a consistent keyring key format
func buildKeyringKey(orgName string, credType CredentialType) string {
	if credType == CredentialTypeToken {
		// For backward compatibility, tokens use just the org name
		return orgName
	}
	return fmt.Sprintf("%s:%s", orgName, string(credType))
}

// NewManager creates a new configuration manager
func NewManager() (*Manager, error) {
	configDir, err := getConfigDir()
	if err != nil {
		return nil, fmt.Errorf("failed to get config directory: %w", err)
	}

	configPath := filepath.Join(configDir, "config.json")

	m := &Manager{
		configPath: configPath,
		config:     &Config{Orgs: make(map[string]*Organization)},
	}

	// Load existing config if it exists
	err = m.Load()
	if err != nil {
		if os.IsNotExist(err) {
			// File doesn't exist yet - this is OK for first-time use
			return m, nil
		}
		// Any other error is fatal - don't continue with empty config
		return nil, fmt.Errorf("failed to load config from %s: %w", configPath, err)
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

	// Create directory if it doesn't exist
	if err := os.MkdirAll(configDir, 0755); err != nil {
		return "", fmt.Errorf("failed to create config directory: %w", err)
	}

	return configDir, nil
}

// Load reads the configuration from disk
func (m *Manager) Load() error {
	data, err := os.ReadFile(m.configPath)
	if err != nil {
		return err
	}

	if err := json.Unmarshal(data, &m.config); err != nil {
		return err
	}

	return nil
}

// Save writes the configuration to disk
func (m *Manager) Save() error {
	data, err := json.MarshalIndent(m.config, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal config: %w", err)
	}

	return os.WriteFile(m.configPath, data, 0600)
}

// GetCurrentOrg returns the current organization
func (m *Manager) GetCurrentOrg() *Organization {
	if m.config.CurrentOrg == "" {
		return nil
	}
	return m.config.Orgs[m.config.CurrentOrg]
}

// GetCurrentOrgToken returns the token for the current organization using keyring-aware retrieval
func (m *Manager) GetCurrentOrgToken() (string, error) {
	org := m.GetCurrentOrg()
	if org == nil {
		return "", fmt.Errorf("no current organization")
	}
	return org.GetTokenWithKeyringDisabled(m.config.DisableKeyring)
}

// SetCurrentOrg sets the current organization
func (m *Manager) SetCurrentOrg(orgName string) error {
	if _, exists := m.config.Orgs[orgName]; !exists {
		return fmt.Errorf("organization %s not found", orgName)
	}
	m.config.CurrentOrg = orgName
	return m.Save()
}

// AddOrg adds a new organization or updates an existing one
func (m *Manager) AddOrg(name, token, url string) error {
	// Validate inputs
	if name == "" {
		return fmt.Errorf("organization name cannot be empty")
	}
	if token == "" {
		return fmt.Errorf("organization token cannot be empty")
	}
	if url == "" {
		return fmt.Errorf("organization URL cannot be empty")
	}

	if m.config.Orgs == nil {
		m.config.Orgs = make(map[string]*Organization)
	}

	// First, check if we already have an organization with this token
	var existingOrgByToken *Organization
	var existingOrgNameByToken string
	for orgName, org := range m.config.Orgs {
		existingToken, err := org.GetTokenWithKeyringDisabled(m.config.DisableKeyring)
		if err == nil && existingToken == token {
			existingOrgByToken = org
			existingOrgNameByToken = orgName
			break
		}
	}

	if existingOrgByToken != nil {
		// Update existing organization found by token
		// If the name changed, we need to move the org to the new key
		if existingOrgNameByToken != name {
			// Remove old entry
			delete(m.config.Orgs, existingOrgNameByToken)
			// Update current org reference if it was pointing to the old name
			if m.config.CurrentOrg == existingOrgNameByToken {
				m.config.CurrentOrg = name
			}
		}

		// Update the organization details
		existingOrgByToken.Name = name
		existingOrgByToken.SetTokenWithKeyringDisabled(token, m.config.DisableKeyring)
		existingOrgByToken.URL = url

		// Store under the correct name
		m.config.Orgs[name] = existingOrgByToken
	} else if existingOrg, exists := m.config.Orgs[name]; exists {
		// Check by name as fallback - update existing organization
		existingOrg.SetTokenWithKeyringDisabled(token, m.config.DisableKeyring)
		existingOrg.URL = url
	} else {
		// Create new organization
		org := &Organization{
			Name: name,
			URL:  url,
		}

		org.SetTokenWithKeyringDisabled(token, m.config.DisableKeyring)
		m.config.Orgs[name] = org

		// Set as current if it's the first org
		if len(m.config.Orgs) == 1 {
			m.config.CurrentOrg = name
		}
	}

	return m.Save()
}

// RemoveOrg removes an organization
func (m *Manager) RemoveOrg(name string) error {
	delete(m.config.Orgs, name)

	// Clear current org if it was removed
	if m.config.CurrentOrg == name {
		m.config.CurrentOrg = ""
	}

	return m.Save()
}

// GetOrgs returns all organizations
func (m *Manager) GetOrgs() map[string]*Organization {
	return m.config.Orgs
}

// GetToken retrieves the token for this organization, checking keyring first, then config file
func (o *Organization) GetToken() (string, error) {
	return o.GetTokenWithKeyringDisabled(false)
}

// GetTokenWithKeyringDisabled retrieves the token with optional keyring bypass
func (o *Organization) GetTokenWithKeyringDisabled(disableKeyring bool) (string, error) {
	if !disableKeyring {
		// Try keyring first
		token, err := keyring.Get(KeyringService, o.Name)
		if err == nil {
			// Check if token is empty even if keyring returned no error
			if token == "" {
				return "", fmt.Errorf("empty token found in keyring for organization %s", o.Name)
			}
			o.UseKeyring = true // Update flag to reflect we're using keyring
			return token, nil
		}
	}

	// Fallback to file-stored token
	if o.Token != "" {
		o.UseKeyring = false // Update flag to reflect we're using file storage
		return o.Token, nil
	}

	return "", fmt.Errorf("no token found for organization %s", o.Name)
}

// SetToken stores the token for this organization, preferring keyring with fallback to config file
func (o *Organization) SetToken(token string) error {
	return o.SetTokenWithKeyringDisabled(token, false)
}

// SetTokenWithKeyringDisabled stores the token with optional keyring bypass
func (o *Organization) SetTokenWithKeyringDisabled(token string, disableKeyring bool) error {
	// Validate token is not empty
	if token == "" {
		return fmt.Errorf("cannot store empty token for organization %s", o.Name)
	}

	if !disableKeyring {
		// Try to store in keyring first
		err := keyring.Set(KeyringService, o.Name, token)
		if err == nil {
			// Successfully stored in keyring
			o.Token = ""        // Clear file-stored token since we're using keyring
			o.UseKeyring = true // Mark that we're using keyring for this org
			return nil
		}
	}

	// Keyring disabled or failed, use file storage
	o.Token = token
	o.UseKeyring = false // Mark that we're using file storage for this org
	return nil
}

// DeleteToken removes the token for this organization from both keyring and config file
func (o *Organization) DeleteToken() error {
	var errors []error

	// Try to delete from keyring (ignore errors if not found)
	if err := keyring.Delete(KeyringService, o.Name); err != nil {
		// Only add to errors if it's not a "not found" type error
		// go-keyring doesn't have a standard "not found" error, so we'll be permissive
		errors = append(errors, fmt.Errorf("keyring delete error: %w", err))
	}

	// Clear file-stored token
	o.Token = ""

	if len(errors) > 0 {
		return fmt.Errorf("token deletion had issues: %v", errors)
	}

	return nil
}

// Enhanced keyring methods for flexible credential management

// FindOrgByToken searches for an organization that has the specified token
func (m *Manager) FindOrgByToken(token string) (*Organization, string, error) {
	for orgName, org := range m.config.Orgs {
		existingToken, err := org.GetToken()
		if err == nil && existingToken == token {
			return org, orgName, nil
		}
	}
	return nil, "", fmt.Errorf("no organization found with the specified token")
}

// GetCredential retrieves a credential of the specified type for the organization
func (o *Organization) GetCredential(credType CredentialType) (string, error) {
	if credType == CredentialTypeToken {
		return o.GetToken()
	}

	key := buildKeyringKey(o.Name, credType)

	// Try keyring first
	credential, err := keyring.Get(KeyringService, key)
	if err == nil {
		return credential, nil
	}

	return "", fmt.Errorf("no %s found for organization %s", credType, o.Name)
}

// SetCredential stores a credential of the specified type for the organization
func (o *Organization) SetCredential(credType CredentialType, credential string) error {
	if credType == CredentialTypeToken {
		return o.SetToken(credential)
	}

	key := buildKeyringKey(o.Name, credType)

	// Try to store in keyring
	err := keyring.Set(KeyringService, key, credential)
	if err != nil {
		return fmt.Errorf("failed to store %s for organization %s: %w", credType, o.Name, err)
	}

	return nil
}

// DeleteCredential removes a credential of the specified type for the organization
func (o *Organization) DeleteCredential(credType CredentialType) error {
	if credType == CredentialTypeToken {
		return o.DeleteToken()
	}

	key := buildKeyringKey(o.Name, credType)

	err := keyring.Delete(KeyringService, key)
	if err != nil {
		return fmt.Errorf("failed to delete %s for organization %s: %w", credType, o.Name, err)
	}

	return nil
}

// ListCredentialTypes returns all credential types stored for this organization
func (o *Organization) ListCredentialTypes() []CredentialType {
	var types []CredentialType

	// Always check for token first
	if _, err := o.GetToken(); err == nil {
		types = append(types, CredentialTypeToken)
	}

	// Check other credential types
	for _, credType := range []CredentialType{CredentialTypeAPIKey, CredentialTypeCert, CredentialTypeSSHKey} {
		if _, err := o.GetCredential(credType); err == nil {
			types = append(types, credType)
		}
	}

	return types
}

// GetAllCredentials returns a map of all credentials for this organization
func (o *Organization) GetAllCredentials() map[CredentialType]string {
	credentials := make(map[CredentialType]string)

	for _, credType := range o.ListCredentialTypes() {
		if cred, err := o.GetCredential(credType); err == nil {
			credentials[credType] = cred
		}
	}

	return credentials
}

// SearchOrgsByURL finds all organizations with the specified URL
func (m *Manager) SearchOrgsByURL(url string) []*Organization {
	var orgs []*Organization
	for _, org := range m.config.Orgs {
		if org.URL == url {
			orgs = append(orgs, org)
		}
	}
	return orgs
}

// SearchOrgsByCredential finds organizations that have a specific credential value
func (m *Manager) SearchOrgsByCredential(credType CredentialType, credential string) []*Organization {
	var orgs []*Organization
	for _, org := range m.config.Orgs {
		if existingCred, err := org.GetCredential(credType); err == nil && existingCred == credential {
			orgs = append(orgs, org)
		}
	}
	return orgs
}

// AddOrgWithoutSetting adds an organization but doesn't set it as current (used for discovery)
func (m *Manager) AddOrgWithoutSetting(name, token, url string) error {
	if m.config.Orgs == nil {
		m.config.Orgs = make(map[string]*Organization)
	}

	// Create new organization
	org := &Organization{
		Name: name,
		URL:  url,
	}

	org.SetTokenWithKeyringDisabled(token, m.config.DisableKeyring)
	m.config.Orgs[name] = org

	// Don't auto-set as current - let user choose through interactive selector
	return m.Save()
}

// AddOrgMetadataOnly adds an organization to config without touching any existing token in keyring
func (m *Manager) AddOrgMetadataOnly(name, url string) error {
	if m.config.Orgs == nil {
		m.config.Orgs = make(map[string]*Organization)
	}

	// Create new organization
	org := &Organization{
		Name:       name,
		URL:        url,
		UseKeyring: true, // Assume keyring usage since we're not storing token
	}

	// Don't call SetToken - leave existing keyring entry untouched
	m.config.Orgs[name] = org

	// Don't auto-set as current - let user choose through interactive selector
	return m.Save()
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
