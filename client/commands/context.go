package commands

import (
	"context"
	"fmt"
	"log/slog"
	"os"
	"path/filepath"
	"strings"

	"github.com/sprite-env/client/config"
	"github.com/sprite-env/client/format"
	"github.com/sprite-env/client/prompts"
)

// GlobalContext contains global state that should be available to all commands
type GlobalContext struct {
	Debug     string // Debug log file path (empty if not debugging)
	ConfigMgr *config.Manager
	Logger    *slog.Logger
}

// IsDebugEnabled returns true if debug logging is enabled
func (gc *GlobalContext) IsDebugEnabled() bool {
	return gc.Debug != ""
}

// handlePromptError checks if an error is from user cancellation and handles it gracefully
func handlePromptError(err error) {
	if err != nil {
		if strings.Contains(err.Error(), "cancelled") {
			fmt.Println("Ok, come back later!")
			os.Exit(1)
		}
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}
}

// PromptForConfirmationOrExit wraps prompts.PromptForConfirmation with cancellation handling
func PromptForConfirmationOrExit(title, description string) bool {
	confirmed, err := prompts.PromptForConfirmation(title, description)
	handlePromptError(err)
	return confirmed
}

// EnsureOrgAndSprite ensures we have an organization and sprite selected.
// It returns the organization and sprite name.
func EnsureOrgAndSprite(cfg *config.Manager, orgOverride, spriteOverride string) (*config.Organization, string, error) {
	// First check if we have environment variables set
	envURL := os.Getenv("SPRITE_URL")
	envToken := os.Getenv("SPRITE_TOKEN")

	var org *config.Organization
	var spriteName string

	// If env vars are set, use them (backward compatibility)
	if envURL != "" && envToken != "" {
		// This is using environment-based config, not org-based
		// Create a temporary org structure
		org = &config.Organization{
			Name:  "env",
			URL:   envURL,
			Token: envToken,
		}
		// For env-based usage, check if sprite override is provided
		if spriteOverride != "" {
			// When using env vars with sprite override, we can track the sprite
			spriteName = spriteOverride
			return org, spriteName, nil
		}
		// Without sprite override, maintain backward compatibility (no sprite tracking)
		return org, "", nil
	}

	// Check if we have command-line overrides
	if orgOverride != "" {
		// Find the organization by name
		orgs := cfg.GetOrgs()
		for _, o := range orgs {
			if o.Name == orgOverride {
				org = o
				// Set as current for this session
				cfg.SetCurrentOrg(o.Name)
				break
			}
		}
		if org == nil {
			return nil, "", fmt.Errorf("organization '%s' not found", orgOverride)
		}
	}

	// If no org override, check .sprite file or use current config
	if org == nil {
		// Check if we have a .sprite file in the current directory or parent directories
		spriteFile, err := config.ReadSpriteFile()
		if err != nil {
			return nil, "", fmt.Errorf("failed to read .sprite file: %w", err)
		}

		// If we have a .sprite file, use it
		if spriteFile != nil {
			// Find the organization
			orgs := cfg.GetOrgs()
			for _, o := range orgs {
				if o.Name == spriteFile.Organization {
					org = o
					// Use sprite name from .sprite file if no override
					if spriteOverride == "" {
						spriteName = spriteFile.Sprite
					}
					break
				}
			}

			if org != nil {
				// Only show .sprite file usage message in debug mode
				logger := slog.Default()
				if logger.Enabled(context.Background(), slog.LevelDebug) {
					fmt.Printf("Using organization '%s' and sprite '%s' from .sprite file\n",
						format.Org(org.Name), format.Sprite(spriteName))
				}
				// Set as current in the config
				cfg.SetCurrentOrg(org.Name)
				// Don't check sprite existence - let API endpoints handle it
			}
		}
	}

	// If still no org, check config or prompt
	if org == nil {
		// Check if we have any organizations configured
		orgs := cfg.GetOrgs()
		if len(orgs) == 0 {
			// Try to discover organizations from keyring first
			discoveredOrg, err := cfg.DiscoverFromKeyring()
			if err == nil && discoveredOrg != nil {
				org = discoveredOrg
			} else {
				// No organizations found - try Fly authentication
				selectedOrg, err := AuthenticateWithFly(cfg)
				if err != nil {
					fmt.Fprintf(os.Stderr, "Error: %v\n", err)
					os.Exit(1)
				}
				org = selectedOrg
			}
		} else {
			// Otherwise, use config-based org selection
			org = cfg.GetCurrentOrg()

			// If no current org, prompt for one
			if org == nil {
				selectedOrg, err := prompts.SelectOrganization(cfg)
				handlePromptError(err)
				org = selectedOrg
			}
		}
	}

	// Handle sprite override
	if spriteOverride != "" {
		spriteName = spriteOverride
		// Don't check sprite existence - let API endpoints handle it
	}

	// If no sprite yet, prompt for one
	if spriteName == "" {
		var err error
		spriteName, err = promptForSpriteName()
		handlePromptError(err)
		// Don't check sprite existence - let API endpoints handle it
	}

	// Save .sprite file if we have both org and sprite and no overrides were used
	if spriteName != "" && org != nil && orgOverride == "" && spriteOverride == "" {
		if err := config.WriteSpriteFile(org.Name, spriteName); err != nil {
			// Log but don't fail - .sprite file is a convenience feature
			slog.Debug("Failed to write .sprite file", "error", err)
		} else {
			// Only show .sprite file creation message in debug mode
			logger := slog.Default()
			if logger.Enabled(context.Background(), slog.LevelDebug) {
				fmt.Printf("Created .sprite file for %s:%s\n",
					format.Org(format.GetOrgDisplayName(org.Name, org.URL)),
					format.Sprite(spriteName))
			}
		}
	}

	return org, spriteName, nil
}

// promptForSpriteName prompts the user to enter a sprite name using huh
func promptForSpriteName() (string, error) {
	spriteName, err := prompts.PromptForSpriteName()
	if err != nil {
		return "", err // Return the error instead of printing and returning empty string
	}
	return spriteName, nil
}

// SaveSprite is now a no-op since we don't store sprites locally
func SaveSprite(cfg *config.Manager, name, id string) error {
	// Check if .sprite file already exists
	existingSpriteFile, _ := config.ReadSpriteFile()
	org := cfg.GetCurrentOrg()

	// Only create .sprite file if it doesn't exist or has different content
	if org != nil {
		needsUpdate := true
		if existingSpriteFile != nil && existingSpriteFile.Organization == org.Name && existingSpriteFile.Sprite == name {
			needsUpdate = false
		}

		if needsUpdate {
			if err := config.WriteSpriteFile(org.Name, name); err != nil {
				slog.Debug("Failed to write .sprite file", "error", err)
			} else {
				// Only show .sprite file update message in debug mode
				logger := slog.Default()
				if logger.Enabled(context.Background(), slog.LevelDebug) {
					fmt.Printf("Updated .sprite file for %s:%s\n",
						format.Org(format.GetOrgDisplayName(org.Name, org.URL)),
						format.Sprite(name))
				}
			}
		}
	}

	return nil
}

// getCurrentDirectory returns the current directory name for display
func getCurrentDirectory() string {
	dir, err := os.Getwd()
	if err != nil {
		return "."
	}
	return filepath.Base(dir)
}
