package config

import (
	"encoding/json"
	"os"
	"path/filepath"
	"testing"

	v0 "github.com/superfly/sprite-env/client/config/v0"
	v1 "github.com/superfly/sprite-env/client/config/v1"
)

func TestDetectConfigVersion(t *testing.T) {
	tests := []struct {
		name     string
		config   interface{}
		expected string
	}{
		{
			name: "v0 config without version field",
			config: v0.Config{
				CurrentOrg: "test-org",
				Orgs: map[string]*v0.Organization{
					"test-org": {
						Name: "test-org",
						URL:  "https://api.example.com",
					},
				},
			},
			expected: ConfigVersionV0,
		},
		{
			name: "v1 config with version field",
			config: v1.Config{
				Version: ConfigVersionV1,
				URLs:    make(map[string]*v1.URLConfig),
			},
			expected: ConfigVersionV1,
		},
		{
			name:     "invalid json",
			config:   "invalid json",
			expected: ConfigVersionV0,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			var data []byte
			var err error

			if s, ok := tt.config.(string); ok {
				data = []byte(s)
			} else {
				data, err = json.Marshal(tt.config)
				if err != nil {
					t.Fatalf("failed to marshal test config: %v", err)
				}
			}

			version := DetectConfigVersion(data)
			if version != tt.expected {
				t.Errorf("expected version %s, got %s", tt.expected, version)
			}
		})
	}
}

func TestMigrateV0ToV1(t *testing.T) {
	tests := []struct {
		name     string
		v0Config v0.Config
		validate func(t *testing.T, v1Config v1.Config)
	}{
		{
			name: "simple migration with one org",
			v0Config: v0.Config{
				CurrentOrg: "test-sprite",
				Orgs: map[string]*v0.Organization{
					"test-sprite": {
						Name:       "test-sprite",
						URL:        "https://api.example.com",
						Token:      "test-token",
						UseKeyring: false,
					},
				},
				DisableKeyring:   false,
				LastVersionCheck: "2024-01-01",
				LatestVersion:    "1.0.0",
				CurrentVersion:   "0.9.0",
			},
			validate: func(t *testing.T, v1Config v1.Config) {
				// Check version
				if v1Config.Version != ConfigVersionV1 {
					t.Errorf("expected version %s, got %s", ConfigVersionV1, v1Config.Version)
				}

				// Check metadata fields
				if v1Config.DisableKeyring != false {
					t.Errorf("DisableKeyring not preserved")
				}
				if v1Config.LastVersionCheck != "2024-01-01" {
					t.Errorf("LastVersionCheck not preserved")
				}
				if v1Config.LatestVersion != "1.0.0" {
					t.Errorf("LatestVersion not preserved")
				}
				if v1Config.CurrentVersion != "0.9.0" {
					t.Errorf("CurrentVersion not preserved")
				}

				// Check URL structure
				urlConfig, exists := v1Config.URLs["https://api.example.com"]
				if !exists {
					t.Fatal("URL not found in migrated config")
				}

				// Check org structure (org name should match sprite name)
				orgConfig, exists := urlConfig.Orgs["test-sprite"]
				if !exists {
					t.Fatal("org 'test-sprite' not found in migrated config")
				}

				// Check sprite structure
				spriteConfig, exists := orgConfig.Sprites["test-sprite"]
				if !exists {
					t.Fatal("sprite not found in migrated config")
				}

				if spriteConfig.Name != "test-sprite" {
					t.Errorf("expected sprite name test-sprite, got %s", spriteConfig.Name)
				}
				// Check org-level token fields
				if orgConfig.Token != "test-token" {
					t.Errorf("token not preserved at org level")
				}
				if orgConfig.UseKeyring != false {
					t.Errorf("UseKeyring not preserved at org level")
				}
				if orgConfig.KeychainKey != "test-sprite" {
					t.Errorf("expected keychain key to be preserved as 'test-sprite' at org level, got %s", orgConfig.KeychainKey)
				}

				// Check current selection
				if v1Config.CurrentSelection == nil {
					t.Fatal("current selection not set")
				}
				if v1Config.CurrentSelection.URL != "https://api.example.com" {
					t.Errorf("current selection URL incorrect")
				}
				if v1Config.CurrentSelection.Org != "test-sprite" {
					t.Errorf("current selection org incorrect")
				}
				// Sprite is no longer in CurrentSelection
			},
		},
		{
			name: "migration with multiple orgs same URL",
			v0Config: v0.Config{
				CurrentOrg: "sprite-prod",
				Orgs: map[string]*v0.Organization{
					"sprite-dev": {
						Name:       "sprite-dev",
						URL:        "https://api.example.com",
						Token:      "dev-token",
						UseKeyring: true,
					},
					"sprite-prod": {
						Name:       "sprite-prod",
						URL:        "https://api.example.com",
						Token:      "",
						UseKeyring: true,
					},
				},
			},
			validate: func(t *testing.T, v1Config v1.Config) {
				// Both sprites should be under the same URL but different orgs now
				urlConfig := v1Config.URLs["https://api.example.com"]
				if urlConfig == nil {
					t.Fatal("URL config not found")
				}

				// Check we have two orgs now
				if len(urlConfig.Orgs) != 2 {
					t.Errorf("expected 2 orgs, got %d", len(urlConfig.Orgs))
				}

				// Check sprite-dev org
				devOrg := urlConfig.Orgs["sprite-dev"]
				if devOrg == nil {
					t.Fatal("sprite-dev org not found")
				}
				if _, exists := devOrg.Sprites["sprite-dev"]; !exists {
					t.Error("sprite-dev not found in sprite-dev org")
				}
				if devOrg.Token != "dev-token" {
					t.Error("dev-token not preserved")
				}
				if devOrg.KeychainKey != "sprite-dev" {
					t.Error("sprite-dev keychain key not preserved")
				}

				// Check sprite-prod org
				prodOrg := urlConfig.Orgs["sprite-prod"]
				if prodOrg == nil {
					t.Fatal("sprite-prod org not found")
				}
				if _, exists := prodOrg.Sprites["sprite-prod"]; !exists {
					t.Error("sprite-prod not found in sprite-prod org")
				}
				if prodOrg.Token != "" {
					t.Error("sprite-prod should have empty token")
				}
				if prodOrg.KeychainKey != "sprite-prod" {
					t.Error("sprite-prod keychain key not preserved")
				}

				// Check current selection is sprite-prod org
				if v1Config.CurrentSelection == nil {
					t.Error("current selection should not be nil")
				}
				if v1Config.CurrentSelection.Org != "sprite-prod" {
					t.Error("current selection org should be sprite-prod")
				}
			},
		},
		{
			name: "migration with different URLs",
			v0Config: v0.Config{
				Orgs: map[string]*v0.Organization{
					"sprite-1": {
						Name: "sprite-1",
						URL:  "https://api1.example.com",
					},
					"sprite-2": {
						Name: "sprite-2",
						URL:  "https://api2.example.com",
					},
				},
			},
			validate: func(t *testing.T, v1Config v1.Config) {
				// Should have 2 different URLs
				if len(v1Config.URLs) != 2 {
					t.Errorf("expected 2 URLs, got %d", len(v1Config.URLs))
				}

				// Check each URL has one org with one sprite
				for url, urlConfig := range v1Config.URLs {
					if len(urlConfig.Orgs) != 1 {
						t.Errorf("URL %s should have 1 org, got %d", url, len(urlConfig.Orgs))
					}

					for _, orgConfig := range urlConfig.Orgs {
						if len(orgConfig.Sprites) != 1 {
							t.Errorf("Org in URL %s should have 1 sprite, got %d", url, len(orgConfig.Sprites))
						}
					}
				}
			},
		},
		{
			name: "migration with keyring usage",
			v0Config: v0.Config{
				Orgs: map[string]*v0.Organization{
					"keyring-sprite": {
						Name:       "keyring-sprite",
						URL:        "https://api.example.com",
						Token:      "", // Empty because it's in keyring
						UseKeyring: true,
					},
				},
				DisableKeyring: false,
			},
			validate: func(t *testing.T, v1Config v1.Config) {
				orgConfig := v1Config.URLs["https://api.example.com"].Orgs["keyring-sprite"]
				if orgConfig == nil {
					t.Fatal("org 'keyring-sprite' not found")
				}

				sprite := orgConfig.Sprites["keyring-sprite"]
				if sprite == nil {
					t.Fatal("sprite not found")
				}

				// Check org-level keyring settings
				if orgConfig.UseKeyring != true {
					t.Error("UseKeyring should be true at org level")
				}
				if orgConfig.Token != "" {
					t.Error("Token should be empty for keyring-based org")
				}
				if orgConfig.KeychainKey != "keyring-sprite" {
					t.Errorf("KeychainKey should be preserved as 'keyring-sprite' at org level, got %s", orgConfig.KeychainKey)
				}
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Marshal v0 config
			v0Data, err := json.Marshal(tt.v0Config)
			if err != nil {
				t.Fatalf("failed to marshal v0 config: %v", err)
			}

			// Migrate
			v1Data, err := migrateV0ToV1(v0Data)
			if err != nil {
				t.Fatalf("migration failed: %v", err)
			}

			// Unmarshal v1 config
			var v1Config v1.Config
			if err := json.Unmarshal(v1Data, &v1Config); err != nil {
				t.Fatalf("failed to unmarshal v1 config: %v", err)
			}

			// Validate
			tt.validate(t, v1Config)
		})
	}
}

func TestMigrateConfig(t *testing.T) {
	tests := []struct {
		name        string
		inputData   string
		expectError bool
	}{
		{
			name: "v0 to v1 migration",
			inputData: `{
				"current_org": "test",
				"orgs": {
					"test": {
						"name": "test",
						"url": "https://api.example.com"
					}
				}
			}`,
			expectError: false,
		},
		{
			name: "v1 no migration needed",
			inputData: `{
				"version": "1",
				"urls": {}
			}`,
			expectError: false,
		},
		{
			name: "unknown version",
			inputData: `{
				"version": "999"
			}`,
			expectError: true,
		},
		{
			name:        "invalid json",
			inputData:   `invalid json`,
			expectError: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result, err := MigrateConfig([]byte(tt.inputData))

			if tt.expectError {
				if err == nil {
					t.Error("expected error but got none")
				}
			} else {
				if err != nil {
					t.Errorf("unexpected error: %v", err)
				}

				// Verify result is valid JSON
				var config map[string]interface{}
				if err := json.Unmarshal(result, &config); err != nil {
					t.Errorf("result is not valid JSON: %v", err)
				}

				// Verify version is set
				if version, ok := config["version"].(string); !ok || version == "" {
					t.Error("migrated config should have version field")
				}
			}
		})
	}
}

func TestBuildKeychainKeyV1(t *testing.T) {
	tests := []struct {
		url      string
		org      string
		sprite   string
		expected string
	}{
		{
			url:      "https://api.example.com",
			org:      "my-org",
			sprite:   "my-sprite",
			expected: "https-api.example.com:my-org:my-sprite",
		},
		{
			url:      "http://localhost:8080",
			org:      "test",
			sprite:   "dev",
			expected: "http-localhost-8080:test:dev",
		},
		{
			url:      "https://api.fly.io/v1/sprites",
			org:      "production",
			sprite:   "app-1",
			expected: "https-api.fly.io-v1-sprites:production:app-1",
		},
	}

	for _, tt := range tests {
		t.Run(tt.expected, func(t *testing.T) {
			result := buildKeychainKeyV1(tt.url, tt.org, tt.sprite)
			if result != tt.expected {
				t.Errorf("expected %s, got %s", tt.expected, result)
			}
		})
	}
}

func TestPerformMigrationIfNeeded(t *testing.T) {
	// Test migration from v0 config.json to v1 sprites.json
	t.Run("v0 to v1 migration", func(t *testing.T) {
		tempDir, err := os.MkdirTemp("", "migration-test")
		if err != nil {
			t.Fatalf("Failed to create temp dir: %v", err)
		}
		defer os.RemoveAll(tempDir)

		// Create a v0 config.json
		oldConfigPath := filepath.Join(tempDir, "config.json")
		oldConfig := v0.Config{
			CurrentOrg: "test-sprite",
			Orgs: map[string]*v0.Organization{
				"test-sprite": {
					Name:       "test-sprite",
					URL:        "https://api.example.com",
					Token:      "test-token",
					UseKeyring: false,
				},
			},
			DisableKeyring: true,
		}

		oldData, _ := json.MarshalIndent(oldConfig, "", "  ")
		if err := os.WriteFile(oldConfigPath, oldData, 0600); err != nil {
			t.Fatalf("Failed to write old config: %v", err)
		}

		// Perform migration
		if err := performMigrationIfNeeded(tempDir); err != nil {
			t.Fatalf("Migration failed: %v", err)
		}

		// Check that config.json still exists (for backward compatibility)
		if _, err := os.Stat(oldConfigPath); err != nil {
			t.Error("config.json should still exist after migration for backward compatibility")
		}

		// Check that sprites.json exists
		newConfigPath := filepath.Join(tempDir, "sprites.json")
		if _, err := os.Stat(newConfigPath); err != nil {
			t.Fatalf("sprites.json should exist after migration: %v", err)
		}

		// Verify content
		data, err := os.ReadFile(newConfigPath)
		if err != nil {
			t.Fatalf("Failed to read sprites.json: %v", err)
		}

		var newConfig v1.Config
		if err := json.Unmarshal(data, &newConfig); err != nil {
			t.Fatalf("Failed to unmarshal sprites.json: %v", err)
		}

		// Check version
		if newConfig.Version != "1" {
			t.Errorf("Expected version 1, got %s", newConfig.Version)
		}

		// Check sprite was migrated
		if len(newConfig.URLs) != 1 {
			t.Errorf("Expected 1 URL, got %d", len(newConfig.URLs))
		}

		urlConfig := newConfig.URLs["https://api.example.com"]
		if urlConfig == nil {
			t.Fatal("URL config not found")
		}

		orgConfig := urlConfig.Orgs["test-sprite"]
		if orgConfig == nil {
			t.Fatal("org 'test-sprite' not found")
		}

		sprite := orgConfig.Sprites["test-sprite"]
		if sprite == nil {
			t.Fatal("sprite not found")
		}

		// Check token at org level
		if orgConfig.Token != "test-token" {
			t.Errorf("Expected token 'test-token' at org level, got '%s'", orgConfig.Token)
		}
	})

	// Test when sprites.json already exists
	t.Run("sprites.json already exists", func(t *testing.T) {
		tempDir, err := os.MkdirTemp("", "migration-test-existing")
		if err != nil {
			t.Fatalf("Failed to create temp dir: %v", err)
		}
		defer os.RemoveAll(tempDir)

		// Create both files
		oldConfigPath := filepath.Join(tempDir, "config.json")
		newConfigPath := filepath.Join(tempDir, "sprites.json")

		// Write old config
		os.WriteFile(oldConfigPath, []byte(`{"current_org": "old"}`), 0600)

		// Write new config
		newConfig := v1.Config{
			Version: "1",
			URLs:    make(map[string]*v1.URLConfig),
		}
		newData, _ := json.MarshalIndent(newConfig, "", "  ")
		os.WriteFile(newConfigPath, newData, 0600)

		// Perform migration - should do nothing
		if err := performMigrationIfNeeded(tempDir); err != nil {
			t.Fatalf("Migration failed: %v", err)
		}

		// Both files should still exist
		if _, err := os.Stat(oldConfigPath); err != nil {
			t.Error("config.json should still exist when sprites.json already exists")
		}
		if _, err := os.Stat(newConfigPath); err != nil {
			t.Error("sprites.json should still exist")
		}
	})

	// Test v1 config.json gets copied to sprites.json
	t.Run("v1 config.json copied to sprites.json", func(t *testing.T) {
		tempDir, err := os.MkdirTemp("", "migration-test-v1")
		if err != nil {
			t.Fatalf("Failed to create temp dir: %v", err)
		}
		defer os.RemoveAll(tempDir)

		// Create a v1 config.json
		oldConfigPath := filepath.Join(tempDir, "config.json")
		v1Config := v1.Config{
			Version: "1",
			URLs: map[string]*v1.URLConfig{
				"https://api.example.com": {
					URL: "https://api.example.com",
					Orgs: map[string]*v1.OrgConfig{
						"my-org": {
							Name:    "my-org",
							Sprites: make(map[string]*v1.SpriteConfig),
						},
					},
				},
			},
		}

		v1Data, _ := json.MarshalIndent(v1Config, "", "  ")
		if err := os.WriteFile(oldConfigPath, v1Data, 0600); err != nil {
			t.Fatalf("Failed to write v1 config: %v", err)
		}

		// Perform migration
		if err := performMigrationIfNeeded(tempDir); err != nil {
			t.Fatalf("Migration failed: %v", err)
		}

		// Check that config.json still exists
		if _, err := os.Stat(oldConfigPath); err != nil {
			t.Error("config.json should still exist after copy")
		}

		// Check that sprites.json exists
		newConfigPath := filepath.Join(tempDir, "sprites.json")
		data, err := os.ReadFile(newConfigPath)
		if err != nil {
			t.Fatal("sprites.json should exist after rename")
		}

		// Verify it's the same content
		var migratedConfig v1.Config
		if err := json.Unmarshal(data, &migratedConfig); err != nil {
			t.Fatalf("Failed to unmarshal sprites.json: %v", err)
		}

		if migratedConfig.Version != "1" {
			t.Error("Version should still be 1 after copy")
		}
	})
}

func TestNewManagerWithMigration(t *testing.T) {
	// Test creating a new manager with migration
	tempDir, err := os.MkdirTemp("", "manager-test")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tempDir)

	// Set HOME to temp dir
	originalHome := os.Getenv("HOME")
	os.Setenv("HOME", tempDir)
	defer os.Setenv("HOME", originalHome)

	// Create .sprites directory with old config
	spritesDir := filepath.Join(tempDir, ".sprites")
	os.MkdirAll(spritesDir, 0755)

	oldConfig := v0.Config{
		CurrentOrg: "my-sprite",
		Orgs: map[string]*v0.Organization{
			"my-sprite": {
				Name:       "my-sprite",
				URL:        "https://api.example.com",
				Token:      "my-token",
				UseKeyring: false,
			},
		},
		DisableKeyring: true,
	}

	oldData, _ := json.MarshalIndent(oldConfig, "", "  ")
	oldConfigPath := filepath.Join(spritesDir, "config.json")
	os.WriteFile(oldConfigPath, oldData, 0600)

	// Create manager - should trigger migration
	mgr, err := NewManager()
	if err != nil {
		t.Fatalf("Failed to create manager: %v", err)
	}

	// Check that config.json still exists
	if _, err := os.Stat(oldConfigPath); err != nil {
		t.Error("config.json should still exist after migration")
	}

	// Check that sprites.json exists
	newConfigPath := filepath.Join(spritesDir, "sprites.json")
	if _, err := os.Stat(newConfigPath); err != nil {
		t.Error("sprites.json should exist after migration")
	}

	// Verify manager has the migrated data
	sprites := mgr.GetAllSprites()
	if len(sprites) != 1 {
		t.Errorf("Expected 1 URL, got %d", len(sprites))
	}

	// Test finding the migrated sprite
	_, url, org, name, err := mgr.FindSprite("my-sprite")
	if err != nil {
		t.Fatalf("Failed to find migrated sprite: %v", err)
	}

	if url != "https://api.example.com" {
		t.Errorf("Wrong URL: %s", url)
	}
	if org != "my-sprite" {
		t.Errorf("Expected org 'my-sprite', got %s", org)
	}
	if name != "my-sprite" {
		t.Errorf("Wrong sprite name: %s", name)
	}

	// Get the token through the compatibility GetOrgs method
	orgs := mgr.GetOrgs()
	if org, exists := orgs["my-sprite"]; exists {
		if org.Token != "my-token" {
			t.Errorf("Wrong token: %s", org.Token)
		}
	} else {
		t.Error("Sprite not found in GetOrgs")
	}
}
