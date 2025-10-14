package config

import (
	"encoding/json"
	"fmt"
	"log/slog"

	v1 "github.com/superfly/sprite-env/client/config/v1"
	"github.com/superfly/sprite-env/client/keyring"
)

// MigrateTokensToKeyring migrates tokens from config file storage to keyring
// This should be called after loading the config but before using it
func (m *Manager) MigrateTokensToKeyring() error {
	var migrated bool

	// Migrate tokens in main config
	for url, urlConfig := range m.config.URLs {
		for orgName, orgConfig := range urlConfig.Orgs {
			if orgConfig.Token != "" {
				slog.Debug("Found token in config, migrating to keyring",
					"url", url,
					"org", orgName,
					"useKeyring", orgConfig.UseKeyring,
					"disableKeyring", m.config.DisableKeyring)

				// Determine keyring service based on UseKeyring flag
				service := KeyringService
				if orgConfig.UserID != "" {
					// Use user-scoped keyring service
					service = fmt.Sprintf("%s:%s", KeyringService, orgConfig.UserID)
				}

				key := orgConfig.KeyringKey
				if key == "" {
					key = orgName // Fallback to org name
				}

				// Store in keyring
				if err := keyring.Set(service, key, orgConfig.Token); err != nil {
					slog.Warn("Failed to migrate token to keyring",
						"error", err,
						"org", orgName,
						"service", service,
						"key", key)
					return fmt.Errorf("failed to migrate token for org %s: %w", orgName, err)
				}

				// Clear the token from config
				orgConfig.Token = ""
				migrated = true

				slog.Info("Migrated token to keyring",
					"org", orgName,
					"service", service,
					"key", key,
					"usingFallback", keyring.IsUsingFallback())
			}
		}
	}

	// Migrate tokens in user config (if loaded)
	if m.userConfig != nil {
		for url, urlConfig := range m.userConfig.URLs {
			for orgName, orgConfig := range urlConfig.Orgs {
				if orgConfig.Token != "" {
					slog.Debug("Found token in user config, migrating to keyring",
						"url", url,
						"org", orgName,
						"userID", m.currentUserID)

					// Use user-scoped keyring service
					service := fmt.Sprintf("%s:%s", KeyringService, m.currentUserID)
					key := orgConfig.KeyringKey
					if key == "" {
						key = orgName // Fallback to org name
					}

					// Store in keyring
					if err := keyring.Set(service, key, orgConfig.Token); err != nil {
						slog.Warn("Failed to migrate token to keyring",
							"error", err,
							"org", orgName,
							"service", service,
							"key", key)
						return fmt.Errorf("failed to migrate token for org %s: %w", orgName, err)
					}

					// Clear the token from config
					orgConfig.Token = ""
					migrated = true

					slog.Info("Migrated token to keyring",
						"org", orgName,
						"service", service,
						"key", key,
						"usingFallback", keyring.IsUsingFallback())
				}
			}
		}
	}

	// Save the config if we migrated any tokens
	if migrated {
		if err := m.Save(); err != nil {
			return fmt.Errorf("failed to save config after token migration: %w", err)
		}
		slog.Info("Token migration complete, config saved")
	}

	return nil
}

// removeTokenFieldsFromJSON removes Token fields from the JSON representation
// This is used when saving config to ensure tokens don't get written back
func removeTokenFieldsFromJSON(data []byte) ([]byte, error) {
	var raw map[string]interface{}
	if err := json.Unmarshal(data, &raw); err != nil {
		return data, err
	}

	// Remove tokens from URLs -> Orgs
	if urls, ok := raw["urls"].(map[string]interface{}); ok {
		for _, urlVal := range urls {
			if urlMap, ok := urlVal.(map[string]interface{}); ok {
				if orgs, ok := urlMap["orgs"].(map[string]interface{}); ok {
					for _, orgVal := range orgs {
						if orgMap, ok := orgVal.(map[string]interface{}); ok {
							delete(orgMap, "token")
						}
					}
				}
			}
		}
	}

	return json.MarshalIndent(raw, "", "  ")
}

// cleanConfigBeforeSave removes UseKeyring flags and ensures no tokens are in config
func cleanConfigBeforeSave(config *v1.Config) {
	for _, urlConfig := range config.URLs {
		for _, orgConfig := range urlConfig.Orgs {
			// Always clear token to prevent it from being saved
			orgConfig.Token = ""
			// Remove UseKeyring flag (no longer needed)
			orgConfig.UseKeyring = false
		}
	}
}
