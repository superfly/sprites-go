package commands

import (
	"fmt"
	"log/slog"
	"os"
	"path/filepath"

	"github.com/sprite-env/client/config"
	"github.com/sprite-env/client/format"
	"github.com/sprite-env/client/prompts"
)

// EnsureOrgAndSprite ensures we have both an organization and sprite selected
// Returns the org and sprite, creating a new sprite if isNew is true
// The orgOverride and spriteOverride parameters allow command-line flags to override config
func EnsureOrgAndSprite(cfg *config.Manager, orgOverride, spriteOverride string) (*config.Organization, *config.Sprite, bool, error) {
	// First check if we have environment variables set
	envURL := os.Getenv("SPRITE_URL")
	envToken := os.Getenv("SPRITE_TOKEN")
	
	var org *config.Organization
	var sprite *config.Sprite
	isNew := false
	
	// If env vars are set, use them (backward compatibility)
	if envURL != "" && envToken != "" {
		// This is using environment-based config, not org-based
		// Create a temporary org structure
		org = &config.Organization{
			Name:  "env",
			URL:   envURL,
			Token: envToken,
		}
		// For env-based usage, we don't track sprites
		return org, nil, false, nil
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
			return nil, nil, false, fmt.Errorf("organization '%s' not found", orgOverride)
		}
	}
	
	// If no org override, check .sprite file or use current config
	if org == nil {
		// Check if we have a .sprite file in the current directory or parent directories
		spriteFile, err := config.ReadSpriteFile()
		if err != nil {
			return nil, nil, false, fmt.Errorf("failed to read .sprite file: %w", err)
		}
		
		// If we have a .sprite file, use it
		if spriteFile != nil {
			// Find the organization
			orgs := cfg.GetOrgs()
			for _, o := range orgs {
				if o.Name == spriteFile.Organization {
					org = o
					// Find the sprite in this org
					if o.Sprites != nil && spriteOverride == "" {
						for _, s := range o.Sprites {
							if s.Name == spriteFile.Sprite {
								sprite = s
								break
							}
						}
					}
					break
				}
			}
			
			// If we found the org but not the sprite, create a placeholder sprite
			// This handles the case where .sprite file references a sprite that hasn't been created yet
			if org != nil && sprite == nil && spriteOverride == "" {
				sprite = &config.Sprite{
					Name: spriteFile.Sprite,
					ID:   "", // No ID yet since it hasn't been created
				}
				isNew = true
				fmt.Printf("Using sprite '%s' from .sprite file (not yet created on server)\n", 
					format.Sprite(sprite.Name))
				// Set as current in the config
				cfg.SetCurrentOrg(org.Name)
				// Don't use SetCurrentSprite as it validates existence
				// Just set the name directly since this is a pending sprite
				if currentOrg := cfg.GetCurrentOrg(); currentOrg != nil {
					currentOrg.CurrentSprite = sprite.Name
				}
			} else if org != nil && sprite != nil {
				// If we found both org and sprite from the file, set them as current
				cfg.SetCurrentOrg(org.Name)
				cfg.SetCurrentSprite(sprite.Name)
			}
		}
	}
	
	// If still no org, check config or prompt
	if org == nil {
		// Check if we have any organizations configured
		orgs := cfg.GetOrgs()
		if len(orgs) == 0 {
			// No organizations configured - prompt for initial login
			selectedOrg, err := prompts.PromptForInitialLogin(cfg)
			if err != nil {
				return nil, nil, false, err
			}
			org = selectedOrg
		} else {
			// Otherwise, use config-based org selection
			org = cfg.GetCurrentOrg()
			
			// If no current org, prompt for one
			if org == nil {
				selectedOrg, err := prompts.SelectOrganization(cfg)
				if err != nil {
					return nil, nil, false, err
				}
				org = selectedOrg
			}
		}
	}
	
	// Handle sprite override
	if spriteOverride != "" {
		// Find the sprite by name in the current org
		if org.Sprites != nil {
			for _, s := range org.Sprites {
				if s.Name == spriteOverride {
					sprite = s
					// Set as current for this session
					cfg.SetCurrentSprite(s.Name)
					break
				}
			}
		}
		if sprite == nil {
			// Create a placeholder sprite for the override
			sprite = &config.Sprite{
				Name: spriteOverride,
				ID:   "", // No ID yet since it hasn't been created
			}
			isNew = true
			fmt.Printf("Sprite '%s' not found in organization, will need to be created\n", 
				format.Sprite(sprite.Name))
		}
	}
	
	// If no sprite yet, get from config or prompt
	if sprite == nil {
		sprite = cfg.GetCurrentSprite()
	}
	
	// If no current sprite, prompt for one
	if sprite == nil {
		selectedSprite, created, err := prompts.SelectOrCreateSprite(cfg, org)
		if err != nil {
			return nil, nil, false, err
		}
		sprite = selectedSprite
		isNew = created
	}
	
	// Save .sprite file if we have both org and sprite and no overrides were used
	// Write it for both new and existing sprites so the directory context is preserved
	if sprite != nil && org != nil && orgOverride == "" && spriteOverride == "" {
		if err := config.WriteSpriteFile(org.Name, sprite.Name); err != nil {
			// Log but don't fail - .sprite file is a convenience feature
			slog.Debug("Failed to write .sprite file", "error", err)
		} else {
			if isNew {
				fmt.Printf("Created .sprite file for %s:%s (pending creation)\n", 
					format.Org(format.GetOrgDisplayName(org.Name, org.URL)), 
					format.Sprite(sprite.Name))
			} else {
				fmt.Printf("Created .sprite file for %s:%s\n", 
					format.Org(format.GetOrgDisplayName(org.Name, org.URL)), 
					format.Sprite(sprite.Name))
			}
		}
	}
	
	return org, sprite, isNew, nil
}

// SaveSprite saves a sprite to the configuration after it's been created
func SaveSprite(cfg *config.Manager, name, id string) error {
	if err := cfg.AddSprite(name, id); err != nil {
		return err
	}
	
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
				fmt.Printf("Updated .sprite file for %s:%s\n", 
					format.Org(format.GetOrgDisplayName(org.Name, org.URL)), 
					format.Sprite(name))
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