package config

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"

	v0 "github.com/superfly/sprite-env/client/config/v0"
	v1 "github.com/superfly/sprite-env/client/config/v1"
)

const (
	// ConfigVersionV0 represents the legacy config format without versioning
	ConfigVersionV0 = "0"
	// ConfigVersionV1 represents the first versioned config with URL->Org->Sprite hierarchy
	ConfigVersionV1 = "1"
	// CurrentConfigVersion is the latest config version
	CurrentConfigVersion = ConfigVersionV1
)

// RawConfig is used to detect the config version
type RawConfig struct {
	Version string `json:"version"`
}

// DetectConfigVersion detects the version of a config file
func DetectConfigVersion(data []byte) string {
	var raw RawConfig
	if err := json.Unmarshal(data, &raw); err != nil {
		// If we can't unmarshal, assume it's v0
		return ConfigVersionV0
	}

	if raw.Version == "" {
		// No version field means v0
		return ConfigVersionV0
	}

	return raw.Version
}

// MigrateConfig migrates a config to the latest version
func MigrateConfig(data []byte) ([]byte, error) {
	version := DetectConfigVersion(data)

	switch version {
	case ConfigVersionV0:
		return migrateV0ToV1(data)
	case ConfigVersionV1:
		// Already at latest version
		return data, nil
	default:
		return nil, fmt.Errorf("unknown config version: %s", version)
	}
}

// migrateV0ToV1 migrates from v0 (legacy) to v1 format
func migrateV0ToV1(data []byte) ([]byte, error) {
	var oldConfig v0.Config
	if err := json.Unmarshal(data, &oldConfig); err != nil {
		return nil, fmt.Errorf("failed to parse v0 config: %w", err)
	}

	// Create new v1 config
	newConfig := v1.Config{
		Version:          ConfigVersionV1,
		URLs:             make(map[string]*v1.URLConfig),
		URLAliases:       make(map[string]string),
		DisableKeyring:   oldConfig.DisableKeyring,
		LastVersionCheck: oldConfig.LastVersionCheck,
		LatestVersion:    oldConfig.LatestVersion,
		CurrentVersion:   oldConfig.CurrentVersion,
	}

	// Migrate organizations
	for orgName, org := range oldConfig.Orgs {
		// In v0, org name was used as both org and sprite name
		// Since v0 didn't have separate org concept, we'll use the sprite name as the org name too
		spriteName := orgName
		migratedOrgName := orgName // Use the same name for org and sprite

		// Ensure we have a URL config for this URL
		if _, exists := newConfig.URLs[org.URL]; !exists {
			newConfig.URLs[org.URL] = &v1.URLConfig{
				URL:  org.URL,
				Orgs: make(map[string]*v1.OrgConfig),
			}
		}

		// Check if this org already exists (in case of name collision)
		if existingOrg, exists := newConfig.URLs[org.URL].Orgs[migratedOrgName]; exists {
			// Org already exists, just add the sprite
			existingOrg.Sprites[spriteName] = &v1.SpriteConfig{
				Name: spriteName,
			}
		} else {
			// Create new org config
			newConfig.URLs[org.URL].Orgs[migratedOrgName] = &v1.OrgConfig{
				Name:        migratedOrgName,
				Token:       org.Token,
				UseKeyring:  org.UseKeyring,
				KeychainKey: orgName, // Preserve the old keychain key for backward compatibility
				Sprites:     make(map[string]*v1.SpriteConfig),
			}

			// Create sprite config
			newConfig.URLs[org.URL].Orgs[migratedOrgName].Sprites[spriteName] = &v1.SpriteConfig{
				Name: spriteName,
			}
		}

		// Set current selection if this was the current org
		if oldConfig.CurrentOrg == orgName {
			newConfig.CurrentSelection = &v1.CurrentSelection{
				URL: org.URL,
				Org: migratedOrgName,
			}
		}
	}

	// Marshal the new config
	return json.MarshalIndent(newConfig, "", "  ")
}

// performMigrationIfNeeded checks if we need to create sprites.json from config.json
// This ensures backward compatibility by keeping config.json for old clients while
// new clients use sprites.json
func performMigrationIfNeeded(configDir string) error {
	oldConfigPath := filepath.Join(configDir, "config.json")
	newConfigPath := filepath.Join(configDir, "sprites.json")

	// If sprites.json already exists, no migration needed
	if _, err := os.Stat(newConfigPath); err == nil {
		return nil
	}

	// If config.json doesn't exist, nothing to migrate
	oldData, err := os.ReadFile(oldConfigPath)
	if err != nil {
		if os.IsNotExist(err) {
			return nil // No old config to migrate
		}
		return fmt.Errorf("failed to read config.json: %w", err)
	}

	// Detect version of old config
	version := DetectConfigVersion(oldData)

	// If it's already v1, just copy to sprites.json
	if version == CurrentConfigVersion {
		// Copy config.json to sprites.json (don't delete original)
		if err := os.WriteFile(newConfigPath, oldData, 0600); err != nil {
			return fmt.Errorf("failed to write sprites.json: %w", err)
		}
		return nil
	}

	// It's v0, need to migrate
	migratedData, err := MigrateConfig(oldData)
	if err != nil {
		return fmt.Errorf("failed to migrate config: %w", err)
	}

	// Write to sprites.json (keep config.json for backward compatibility)
	if err := os.WriteFile(newConfigPath, migratedData, 0600); err != nil {
		return fmt.Errorf("failed to write sprites.json: %w", err)
	}

	// Note: We intentionally keep config.json for backward compatibility with old clients

	return nil
}
