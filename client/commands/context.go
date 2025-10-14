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
	"github.com/superfly/sprite-env/client/orgresolve"
	"github.com/superfly/sprite-env/client/prompts"
	sprites "github.com/superfly/sprites-go"
)

// GlobalContext contains global state that should be available to all commands
type GlobalContext struct {
	Debug          string // Debug log file path (empty if not debugging)
	ConfigMgr      *config.Manager
	Logger         *slog.Logger
	OrgOverride    string // Organization override from global flags
	SpriteOverride string // Sprite override from global flags
	Version        string // Embedded version from build
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
	// Check for environment variables that might provide a default URL
	envURL := os.Getenv("SPRITE_URL")
	if envURL == "" {
		envURL = os.Getenv("SPRITES_API_URL")
	}
	envToken := os.Getenv("SPRITE_TOKEN")

	var org *config.Organization

	// Check if we have command-line overrides
	if orgOverride != "" {
		// Try to find the organization with alias support
		foundOrg, foundURL, err := cfg.FindOrgWithAlias(orgOverride)
		if err != nil {
			// Check if it's an unknown alias error
			if strings.Contains(err.Error(), "unknown alias:") {
				// Parse the org specification to get the alias
				_, alias, _ := cfg.ParseOrgWithAlias(orgOverride)

				// Get all available URLs
				urls := cfg.GetAllURLs()
				if len(urls) > 0 {
					// In non-interactive contexts, we can't prompt, so return error
					return nil, fmt.Errorf("unknown alias '%s'. Available URLs: %v", alias, urls)
				} else {
					return nil, fmt.Errorf("no URLs configured to associate with alias '%s'", alias)
				}
			}
			return nil, err
		}

		org = foundOrg
		// Parse to get the alias that was used
		_, alias, _ := cfg.ParseOrgWithAlias(orgOverride)
		slog.Default().Debug("Found org via FindOrgWithAlias", "orgOverride", orgOverride, "orgName", org.Name, "orgURL", org.URL, "foundURL", foundURL, "alias", alias)
		// Set as current for this session
		if err := cfg.SetCurrentOrg(org.Name); err != nil {
			return nil, fmt.Errorf("failed to set current org: %w", err)
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
			// If we have an environment URL, use it as a default
			if envURL != "" {
				// Create a temporary org structure
				org = &config.Organization{
					Name:  "default",
					URL:   envURL,
					Token: envToken, // Will be empty if not set
				}
				// This org is not saved to config, just used for this session
				return org, nil
			}
			return nil, fmt.Errorf("no organizations configured. Please run 'sprite org auth' first")
		}

		// Check if all orgs are from the same URL (single API endpoint)
		urls := make(map[string]bool)
		for _, o := range orgs {
			urls[o.URL] = true
		}

		if len(urls) == 1 {
			// All orgs are from the same URL, use any of them
			for _, o := range orgs {
				org = o
				break
			}
		} else if envURL != "" {
			// Multiple URLs configured, but we have an environment URL
			// Create a temporary org for the environment URL
			org = &config.Organization{
				Name:  "default",
				URL:   envURL,
				Token: envToken, // Will be empty if not set
			}
		} else {
			// Multiple URLs and no environment URL, use the first org
			for _, o := range orgs {
				org = o
				break
			}
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

	// Check for environment variables that might provide a default URL
	envURL := os.Getenv("SPRITE_URL")
	if envURL == "" {
		envURL = os.Getenv("SPRITES_API_URL")
	}
	envToken := os.Getenv("SPRITE_TOKEN")
	slog.Debug("Environment variables check", "envURL", envURL != "", "SPRITE_TOKEN", envToken != "")

	// Check if we have command-line overrides
	if orgOverride != "" {
		slog.Debug("Checking for org override", "orgOverride", orgOverride)

		// Try to find the organization with alias support
		foundOrg, foundURL, err := ctx.ConfigMgr.FindOrgWithAlias(orgOverride)
		if err != nil {
			// Check if it's an unknown alias error
			if strings.Contains(err.Error(), "unknown alias:") {
				// Parse the org specification to get the alias
				_, alias, _ := ctx.ConfigMgr.ParseOrgWithAlias(orgOverride)

				// Get all available URLs
				urls := ctx.ConfigMgr.GetAllURLs()
				if len(urls) > 0 {
					// Prompt user to select a URL for this alias
					selectedURL, promptErr := prompts.SelectURLForAlias(alias, urls)
					if promptErr != nil {
						return nil, "", fmt.Errorf("failed to select URL for alias: %w", promptErr)
					}

					// Save the alias
					if saveErr := ctx.ConfigMgr.SetURLAlias(alias, selectedURL); saveErr != nil {
						return nil, "", fmt.Errorf("failed to save alias: %w", saveErr)
					}

					fmt.Printf("%s Saved alias '%s' for URL %s\n",
						format.Success("✓"),
						format.Bold(alias),
						format.URL(selectedURL))

					// Try again with the newly saved alias
					foundOrg, foundURL, err = ctx.ConfigMgr.FindOrgWithAlias(orgOverride)
					if err != nil {
						return nil, "", err
					}
				} else {
					return nil, "", fmt.Errorf("no URLs configured to associate with alias '%s'", alias)
				}
			} else {
				return nil, "", err
			}
		}

		org = foundOrg
		// Set as current for this session
		if err := ctx.ConfigMgr.SetCurrentOrg(org.Name); err != nil {
			return nil, "", fmt.Errorf("failed to set current org: %w", err)
		}
		slog.Debug("Found organization from override", "org", org.Name, "url", foundURL)
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
				// If environment URL is set, create a temporary org with the env URL
				if envURL != "" {
					slog.Debug("Found org from .sprite file but using environment URL", "org", org.Name, "configURL", org.URL, "envURL", envURL)
					org = &config.Organization{
						Name:  org.Name, // Keep the org name from .sprite file
						URL:   envURL,   // Use the environment URL
						Token: envToken, // Use environment token if available
					}
				}

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
				// Set as current in the config (unless using env URL)
				if envURL == "" {
					if err := ctx.ConfigMgr.SetCurrentOrg(org.Name); err != nil {
						return nil, "", fmt.Errorf("failed to set current org: %w", err)
					}
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
				// If we have an environment URL, use it as a default
				if envURL != "" {
					slog.Debug("No orgs configured, but have environment URL", "url", envURL)
					// Create a temporary org structure
					org = &config.Organization{
						Name:  "default",
						URL:   envURL,
						Token: envToken, // Will be empty if not set
					}
					// This org is not saved to config, just used for this session
				} else {
					return nil, "", fmt.Errorf("no organizations configured. Please run 'sprite org auth' first")
				}
			} else {
				// Check if all orgs are from the same URL (single API endpoint)
				urls := make(map[string]bool)
				for _, o := range orgs {
					urls[o.URL] = true
				}

				if len(urls) == 1 {
					// All orgs are from the same URL, use any of them
					for _, o := range orgs {
						org = o
						slog.Debug("Using org from single API endpoint", "org", o.Name, "url", o.URL)
						break
					}
				} else if envURL != "" {
					// Multiple URLs configured, but we have an environment URL
					// Create a temporary org for the environment URL
					slog.Debug("Multiple URLs configured, using environment URL", "url", envURL)
					org = &config.Organization{
						Name:  "default",
						URL:   envURL,
						Token: envToken, // Will be empty if not set
					}
				} else {
					// Multiple URLs and no environment URL, use the first org
					for _, o := range orgs {
						org = o
						slog.Debug("Using first available org", "org", o.Name, "url", o.URL)
						break
					}
				}
			}
		} else {
			slog.Debug("Using current org", "org", org.Name, "url", org.URL)
			// If environment URL is set, override the org's URL
			if envURL != "" {
				slog.Debug("Overriding current org URL with environment URL", "org", org.Name, "configURL", org.URL, "envURL", envURL)
				org = &config.Organization{
					Name:  org.Name, // Keep the org name
					URL:   envURL,   // Use the environment URL
					Token: envToken, // Use environment token if available
				}
			}
		}
	}

	// If we have a sprite override, use it
	if spriteOverride != "" {
		spriteName = spriteOverride
		slog.Debug("Using sprite override", "sprite", spriteName)
	}

	// If we have an org but no sprite name, prompt for it
	if spriteName == "" && org != nil {
		var err error
		spriteName, err = promptForSpriteName()
		if err != nil {
			return nil, "", err
		}
		slog.Debug("Got sprite name from prompt", "sprite", spriteName)
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

// GetOrgAndClient returns the selected organization and a configured sprites client.
// This is the unified function that all commands should use for organization selection
// and client creation. It handles all the complex logic for org selection, aliases,
// environment variables, .sprite files, and client configuration.
func GetOrgAndClient(ctx *GlobalContext, orgOverride string) (*config.Organization, *sprites.Client, error) {
	// Use global context override if available
	if ctx.OrgOverride != "" {
		orgOverride = ctx.OrgOverride
	}

	// Get the organization using the existing logic
	org, err := getOrganization(ctx, orgOverride)
	if err != nil {
		// If we have a TTY and the error is about missing orgs/auth, run auth flow directly
		if IsTTY() {
			if strings.Contains(err.Error(), "no organizations configured") ||
				strings.Contains(err.Error(), "no active user") {
				fmt.Println()
				// Just start the auth flow directly (don't ask y/n)
				return SelectOrganization(ctx)
			}
			
			// For "not found" errors, use the nice prompt
			if strings.Contains(err.Error(), "not found") {
				fmt.Println()
				confirmed, promptErr := prompts.PromptToAuthenticate()
				if promptErr != nil {
					return nil, nil, promptErr
				}
				if confirmed {
					return SelectOrganization(ctx)
				}
			}
		}

		// Return helpful error message for non-TTY
		if strings.Contains(err.Error(), "no organizations configured") {
			return nil, nil, fmt.Errorf("no organizations configured. Run 'sprite login' to authenticate")
		}
		if strings.Contains(err.Error(), "no active user") {
			return nil, nil, fmt.Errorf("no active user. Run 'sprite login' to authenticate")
		}

		return nil, nil, err
	}

	// Get auth token
	token, err := org.GetToken()
	if err != nil {
		// If token retrieval fails and we have TTY, use nice prompt to re-authenticate
		if IsTTY() && strings.Contains(err.Error(), "no token found") {
			fmt.Println()
			confirmed, promptErr := prompts.PromptToReAuthenticate(org.Name)
			if promptErr != nil {
				return nil, nil, promptErr
			}
			if confirmed {
				return SelectOrganization(ctx)
			}
			return nil, nil, fmt.Errorf("authentication required")
		}

		return nil, nil, fmt.Errorf("failed to get auth token: %w. Run 'sprite login' to authenticate", err)
	}

	// Create and configure sprites client
	client := sprites.New(token, sprites.WithBaseURL(getSpritesAPIURL(org)))

	return org, client, nil
}

// getOrganization handles all organization selection logic in one place.
// This consolidates the logic from EnsureOrg and EnsureOrgAndSpriteWithContext.
func getOrganization(ctx *GlobalContext, orgOverride string) (*config.Organization, error) {
	// Defer to centralized resolver so logic is testable without importing this package
	org, err := orgresolve.ResolveOrg(ctx.ConfigMgr, orgOverride)
	if err != nil {
		return nil, err
	}
	slog.Debug("Final organization selection", "org", org.Name, "url", org.URL)
	return org, nil
}

// GetOrgClientAndSprite returns the selected organization, configured sprites client, and sprite instance.
// This is the unified function that all commands should use for organization selection,
// client creation, and sprite selection. It handles all the complex logic for org selection,
// aliases, environment variables, .sprite files, client configuration, and sprite selection.
func GetOrgClientAndSprite(ctx *GlobalContext, orgOverride, spriteOverride string) (*config.Organization, *sprites.Client, *sprites.Sprite, error) {
	// Get organization and client using existing unified function
	org, client, err := GetOrgAndClient(ctx, orgOverride)
	if err != nil {
		return nil, nil, nil, err
	}

	// Get sprite name using existing logic
	spriteName, err := getSpriteName(ctx, spriteOverride)
	if err != nil {
		return nil, nil, nil, err
	}

	// Create sprite instance with organization information
	orgInfo := &sprites.OrganizationInfo{
		Name: org.Name,
		URL:  org.URL,
	}
	sprite := client.SpriteWithOrg(spriteName, orgInfo)

	return org, client, sprite, nil
}

// getSpriteName handles sprite name selection logic, similar to EnsureOrgAndSpriteWithContext
func getSpriteName(ctx *GlobalContext, spriteOverride string) (string, error) {
	// Use global context override if available
	if ctx.SpriteOverride != "" {
		spriteOverride = ctx.SpriteOverride
	}

	var spriteName string

	// Check .sprite file for sprite name if no override
	if spriteOverride == "" {
		spriteFile, _, err := config.ReadSpriteFile()
		if err == nil && spriteFile != nil && spriteFile.Sprite != "" {
			spriteName = spriteFile.Sprite
			slog.Debug("Found sprite name from .sprite file", "sprite", spriteName)
		}
	} else {
		spriteName = spriteOverride
		slog.Debug("Using sprite override", "sprite", spriteName)
	}

	// If we still don't have a sprite name, prompt for it
	if spriteName == "" {
		var err error
		spriteName, err = promptForSpriteName()
		if err != nil {
			return "", err
		}
		slog.Debug("Got sprite name from prompt", "sprite", spriteName)
	}

	slog.Debug("Final sprite selection", "sprite", spriteName)
	return spriteName, nil
}
