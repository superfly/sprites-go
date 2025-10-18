package orgresolve

import (
	"fmt"
	"log/slog"
	"os"

	"github.com/superfly/sprite-env/client/config"
)

// ResolveOrg implements client-side organization resolution according to spec:
// - "-o <api>:<org>" looks up API alias and organization under that API
// - "-o <org>" defaults to https://api.sprites.dev
// - No -o: defaults to https://api.sprites.dev API and prompts/selects org via config
// - SPRITE_ORG is used when no -o is provided
// Notes: This package is UI-agnostic; prompting is handled by callers if needed.
func ResolveOrg(cfg *config.Manager, orgOverride string) (*config.Organization, error) {
	// Environment variables that may influence URL or token
	envURL := os.Getenv("SPRITE_URL")
	if envURL == "" {
		envURL = os.Getenv("SPRITES_API_URL")
	}
	envToken := os.Getenv("SPRITE_TOKEN")

	// Allow SPRITE_ORG to specify org when -o not provided
	if orgOverride == "" {
		if envOrg := os.Getenv("SPRITE_ORG"); envOrg != "" {
			orgOverride = envOrg
		}
	}

	const defaultAPI = "https://api.sprites.dev"

	var org *config.Organization

	// If an override is provided, resolve it first
	if orgOverride != "" {
		// Check alias pattern alias:org
		parsedOrg, alias, hasAlias := cfg.ParseOrgWithAlias(orgOverride)
		if hasAlias {
			// Use existing alias resolution. Caller may handle prompting for unknown alias.
			foundOrg, foundURL, err := cfg.FindOrgWithAlias(orgOverride)
			if err != nil {
				// Keep error context concise
				return nil, err
			}
			// Ensure current selection matches exact URL and org
			if err := cfg.SetCurrentSelection(foundURL, foundOrg.Name); err != nil {
				return nil, fmt.Errorf("failed to set current org: %w", err)
			}
			slog.Debug("Resolved org with alias", "alias", alias, "org", foundOrg.Name, "url", foundURL)
			return foundOrg, nil
		}

		// No alias provided: honor environment URL if present for this session
		if envURL != "" {
			// Find the org by name from config (any URL) to preserve keyring linkage
			foundOrg, _, err := cfg.FindOrgWithAlias(parsedOrg)
			if err == nil && foundOrg != nil {
				// Override URL for this session only; do not change current selection
				originalURL := foundOrg.URL
				foundOrg.URL = envURL
				slog.Debug("Resolved org with env URL override", "org", foundOrg.Name, "configURL", originalURL, "envURL", envURL)
				return foundOrg, nil
			}
			// If not found anywhere, fall through to default behavior
		}

		// Fallback: use default public API endpoint
		foundOrg, err := cfg.FindOrgAtURL(defaultAPI, parsedOrg)
		if err != nil {
			return nil, err
		}
		if err := cfg.SetCurrentSelection(defaultAPI, foundOrg.Name); err != nil {
			return nil, fmt.Errorf("failed to set current org: %w", err)
		}
		slog.Debug("Resolved org at default API", "org", foundOrg.Name, "url", defaultAPI)
		return foundOrg, nil
	}

	// No override: attempt .sprite file
	if spriteFile, _, err := config.ReadSpriteFile(); err == nil && spriteFile != nil && spriteFile.Organization != "" {
		// Look up org by name across configured URLs
		orgs := cfg.GetOrgs()
		for _, o := range orgs {
			if o.Name == spriteFile.Organization {
				org = o
				break
			}
		}
		if org != nil {
			// If envURL provided, use it for this session only
			if envURL != "" {
				org = &config.Organization{
					Name:  org.Name,
					URL:   envURL,
					Token: envToken,
				}
			} else {
				_ = cfg.SetCurrentOrg(org.Name)
			}
			return org, nil
		}
	}

	// Fall back to available orgs
	orgs := cfg.GetOrgs()
	if len(orgs) == 0 {
		if envURL != "" {
			return &config.Organization{Name: "default", URL: envURL, Token: envToken}, nil
		}
		return nil, fmt.Errorf("no organizations configured. Please run 'sprite org auth' first")
	}

	// Prefer orgs under the default API first
	for _, o := range orgs {
		if o.URL == defaultAPI {
			return o, nil
		}
	}

	// Otherwise prefer current if set
	if current := cfg.GetCurrentOrg(); current != nil {
		return current, nil
	}

	// As a last resort, return the first available org
	for _, o := range orgs {
		return o, nil
	}

	return nil, fmt.Errorf("no organizations available")
}
