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

// EnsureOrg ensures we have a valid organization for API calls.
// It returns the organization.
func EnsureOrg(cfg *config.Manager, orgOverride string) (*config.Organization, error) {
	// First check if we have environment variables set
	envURL := os.Getenv("SPRITE_URL")
	envToken := os.Getenv("SPRITE_TOKEN")

	var org *config.Organization

	// If env vars are set, use them (backward compatibility)
	if envURL != "" && envToken != "" {
		// This is using environment-based config, not org-based
		// Create a temporary org structure
		org = &config.Organization{
			Name:  "env",
			URL:   envURL,
			Token: envToken,
		}
		return org, nil
	}

	// Check if we have command-line overrides
	if orgOverride != "" {
		// Find the organization by name
		orgs := cfg.GetOrgs()
		for _, o := range orgs {
			if o.Name == orgOverride {
				org = o
				// Set as current for this session
				if err := cfg.SetCurrentOrg(o.Name); err != nil {
					return nil, fmt.Errorf("failed to set current org: %w", err)
				}
				break
			}
		}
		if org == nil {
			return nil, fmt.Errorf("organization '%s' not found", orgOverride)
		}
		return org, nil
	}

	// Check .sprite file for organization
	spriteFile, _, err := config.ReadSpriteFile()
	if err == nil && spriteFile != nil && spriteFile.Organization != "" {
		// Find the organization
		orgs := cfg.GetOrgs()
		for _, o := range orgs {
			if o.Name == spriteFile.Organization {
				return o, nil
			}
		}
	}

	// Use current organization
	org = cfg.GetCurrentOrg()
	if org == nil {
		// If no current org, try to get the first available one
		orgs := cfg.GetOrgs()
		if len(orgs) == 0 {
			return nil, fmt.Errorf("no organizations configured. Please run 'sprite org auth' first")
		}
		// Get the first org from the map
		for _, o := range orgs {
			org = o
			break
		}
	}

	return org, nil
}

// EnsureOrgAndSprite ensures we have valid organization and sprite for API calls.
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
				if err := cfg.SetCurrentOrg(o.Name); err != nil {
					return nil, "", fmt.Errorf("failed to set current org: %w", err)
				}
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
		spriteFile, spritePath, err := config.ReadSpriteFile()
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
				// Print where we loaded the sprite from
				if spritePath != "" && spriteName != "" {
					fmt.Printf("Using %s %s (from %s)\n",
						format.Org(format.GetOrgDisplayName(org.Name, org.URL)),
						format.Sprite(spriteName),
						format.Subtle(spritePath))
				}
				// Only show .sprite file usage message in debug mode
				logger := slog.Default()
				if logger.Enabled(context.Background(), slog.LevelDebug) {
					fmt.Printf("Using organization '%s' and sprite '%s' from .sprite file\n",
						format.Org(org.Name), format.Sprite(spriteName))
				}
				// Set as current in the config
				if err := cfg.SetCurrentOrg(org.Name); err != nil {
					return nil, "", fmt.Errorf("failed to set current org: %w", err)
				}
				// Don't check sprite existence - let API endpoints handle it
			}
		}
	}

	// If still no org, check config or prompt
	if org == nil {
		// Check if we have any organizations configured
		orgs := cfg.GetOrgs()
		if len(orgs) == 0 {
			// No organizations found - try Fly authentication
			selectedOrg, err := AuthenticateWithFly(cfg)
			if err != nil {
				fmt.Fprintf(os.Stderr, "Error: %v\n", err)
				os.Exit(1)
			}
			org = selectedOrg
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
	// Sprites are no longer stored in local config
	// They are fetched from API when needed or passed through to API calls
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
