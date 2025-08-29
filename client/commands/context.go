package commands

import (
	"context"
	"fmt"
	"log/slog"
	"os"
	"path/filepath"
	"strings"

	"github.com/superfly/sprite-env/client/config"
	"github.com/superfly/sprite-env/client/format"
	"github.com/superfly/sprite-env/client/prompts"
)

// GlobalContext contains global state that should be available to all commands
type GlobalContext struct {
	Debug          string // Debug log file path (empty if not debugging)
	ConfigMgr      *config.Manager
	Logger         *slog.Logger
	OrgOverride    string // Organization override from global flags
	SpriteOverride string // Sprite override from global flags
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
	return EnsureOrgAndSpriteWithContext(&GlobalContext{ConfigMgr: cfg}, orgOverride, spriteOverride)
}

// EnsureOrgAndSpriteWithContext ensures we have valid organization and sprite for API calls.
// It returns the organization and sprite name, using global overrides from the context.
func EnsureOrgAndSpriteWithContext(ctx *GlobalContext, orgOverride, spriteOverride string) (*config.Organization, string, error) {
	// Debug logging
	slog.Debug("EnsureOrgAndSpriteWithContext called",
		"orgOverride", orgOverride,
		"spriteOverride", spriteOverride,
		"ctx.OrgOverride", ctx.OrgOverride,
		"ctx.SpriteOverride", ctx.SpriteOverride)

	// Use global overrides if available
	if ctx.OrgOverride != "" {
		slog.Debug("Using org override from context", "org", ctx.OrgOverride)
		orgOverride = ctx.OrgOverride
	}
	if ctx.SpriteOverride != "" {
		slog.Debug("Using sprite override from context", "sprite", ctx.SpriteOverride)
		spriteOverride = ctx.SpriteOverride
	}

	var org *config.Organization
	var spriteName string

	// Only use environment variables if no org or sprite override is specified
	// This allows users to override environment variables with explicit flags
	envURL := os.Getenv("SPRITE_URL")
	envToken := os.Getenv("SPRITE_TOKEN")
	slog.Debug("Environment variables check", "SPRITE_URL", envURL != "", "SPRITE_TOKEN", envToken != "")

	// If we have a sprite override but no org override, we should NOT use env vars
	// Instead, we should use configured organizations
	if spriteOverride != "" && orgOverride == "" && envURL != "" && envToken != "" {
		slog.Debug("Sprite override specified with env vars present - ignoring env vars to use configured orgs")
		// Don't use env vars, continue to org selection below
	} else if envURL != "" && envToken != "" && orgOverride == "" && spriteOverride == "" {
		// Only use env vars for backward compatibility when no overrides are specified
		slog.Debug("Using environment variables for organization (no overrides specified)")
		// This is using environment-based config, not org-based
		// Create a temporary org structure
		org = &config.Organization{
			Name:  "env",
			URL:   envURL,
			Token: envToken,
		}
		// Without sprite override, maintain backward compatibility (no sprite tracking)
		slog.Debug("Returning env-based org without sprite", "org", "env")
		return org, "", nil
	}

	// Check if we have command-line overrides
	if orgOverride != "" {
		slog.Debug("Checking for org override", "orgOverride", orgOverride)
		// Find the organization by name
		orgs := ctx.ConfigMgr.GetOrgs()
		for _, o := range orgs {
			if o.Name == orgOverride {
				org = o
				// Set as current for this session
				if err := ctx.ConfigMgr.SetCurrentOrg(o.Name); err != nil {
					return nil, "", fmt.Errorf("failed to set current org: %w", err)
				}
				slog.Debug("Found organization from override", "org", o.Name, "url", o.URL)
				break
			}
		}
		if org == nil {
			return nil, "", fmt.Errorf("organization '%s' not found", orgOverride)
		}
	}

	// If no org override, check .sprite file or use current config
	if org == nil {
		slog.Debug("No org override, checking .sprite file")
		// Check if we have a .sprite file in the current directory or parent directories
		spriteFile, spritePath, err := config.ReadSpriteFile()
		if err != nil {
			return nil, "", fmt.Errorf("failed to read .sprite file: %w", err)
		}

		// If we have a .sprite file, use it
		if spriteFile != nil {
			slog.Debug("Found .sprite file", "path", spritePath, "org", spriteFile.Organization, "sprite", spriteFile.Sprite)
			// Find the organization
			orgs := ctx.ConfigMgr.GetOrgs()
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
				if err := ctx.ConfigMgr.SetCurrentOrg(org.Name); err != nil {
					return nil, "", fmt.Errorf("failed to set current org: %w", err)
				}
				// Don't check sprite existence - let API endpoints handle it
			}
		}
	}

	// If still no org, check config or prompt
	if org == nil {
		slog.Debug("No org from .sprite file, checking current org")
		// Use current organization
		org = ctx.ConfigMgr.GetCurrentOrg()
		if org == nil {
			slog.Debug("No current org, checking available orgs")
			// If no current org, try to get the first available one
			orgs := ctx.ConfigMgr.GetOrgs()
			if len(orgs) == 0 {
				return nil, "", fmt.Errorf("no organizations configured. Please run 'sprite org auth' first")
			}
			// Get the first org from the map
			for _, o := range orgs {
				org = o
				slog.Debug("Using first available org", "org", o.Name, "url", o.URL)
				break
			}
		} else {
			slog.Debug("Using current org", "org", org.Name, "url", org.URL)
		}
	}

	// If we have a sprite override, use it
	if spriteOverride != "" {
		spriteName = spriteOverride
		slog.Debug("Using sprite override", "sprite", spriteName)
	}

	slog.Debug("Final result", "org", org.Name, "url", org.URL, "sprite", spriteName)
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
