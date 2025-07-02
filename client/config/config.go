package config

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"runtime"
)

// Config represents the sprite configuration
type Config struct {
	CurrentOrg string                    `json:"current_org,omitempty"`
	Orgs       map[string]*Organization  `json:"orgs"`
}

// Organization represents an organization configuration
type Organization struct {
	Name        string              `json:"name"`
	Token       string              `json:"token"`
	URL         string              `json:"url"`
	CurrentSprite string            `json:"current_sprite,omitempty"`
	Sprites     map[string]*Sprite  `json:"sprites"`
}

// Sprite represents a sprite configuration
type Sprite struct {
	Name string `json:"name"`
	ID   string `json:"id,omitempty"`
}

// Manager handles configuration operations
type Manager struct {
	configPath string
	config     *Config
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
	if err := m.Load(); err != nil && !os.IsNotExist(err) {
		return nil, fmt.Errorf("failed to load config: %w", err)
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
	
	return json.Unmarshal(data, &m.config)
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

// SetCurrentOrg sets the current organization
func (m *Manager) SetCurrentOrg(orgName string) error {
	if _, exists := m.config.Orgs[orgName]; !exists {
		return fmt.Errorf("organization %s not found", orgName)
	}
	m.config.CurrentOrg = orgName
	return m.Save()
}

// AddOrg adds a new organization
func (m *Manager) AddOrg(name, token, url string) error {
	if m.config.Orgs == nil {
		m.config.Orgs = make(map[string]*Organization)
	}
	
	org := &Organization{
		Name:    name,
		Token:   token,
		URL:     url,
		Sprites: make(map[string]*Sprite),
	}
	
	m.config.Orgs[name] = org
	
	// Set as current if it's the first org
	if len(m.config.Orgs) == 1 {
		m.config.CurrentOrg = name
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

// GetCurrentSprite returns the current sprite for the current org
func (m *Manager) GetCurrentSprite() *Sprite {
	org := m.GetCurrentOrg()
	if org == nil || org.CurrentSprite == "" {
		return nil
	}
	return org.Sprites[org.CurrentSprite]
}

// SetCurrentSprite sets the current sprite for the current org
func (m *Manager) SetCurrentSprite(spriteName string) error {
	org := m.GetCurrentOrg()
	if org == nil {
		return fmt.Errorf("no current organization")
	}
	
	if _, exists := org.Sprites[spriteName]; !exists {
		return fmt.Errorf("sprite %s not found", spriteName)
	}
	
	org.CurrentSprite = spriteName
	return m.Save()
}

// AddSprite adds a new sprite to the current org
func (m *Manager) AddSprite(name, id string) error {
	org := m.GetCurrentOrg()
	if org == nil {
		return fmt.Errorf("no current organization")
	}
	
	if org.Sprites == nil {
		org.Sprites = make(map[string]*Sprite)
	}
	
	org.Sprites[name] = &Sprite{
		Name: name,
		ID:   id,
	}
	
	// Set as current if it's the first sprite
	if len(org.Sprites) == 1 {
		org.CurrentSprite = name
	}
	
	return m.Save()
}

// RemoveSprite removes a sprite from the current org
func (m *Manager) RemoveSprite(name string) error {
	org := m.GetCurrentOrg()
	if org == nil {
		return fmt.Errorf("no current organization")
	}
	
	delete(org.Sprites, name)
	
	// Clear current sprite if it was removed
	if org.CurrentSprite == name {
		org.CurrentSprite = ""
	}
	
	return m.Save()
}