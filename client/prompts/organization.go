package prompts

import (
	"context"
	"fmt"
	"log/slog"

	"github.com/charmbracelet/huh"
	"github.com/superfly/sprite-env/client/config"
	"github.com/superfly/sprite-env/client/format"
)

// SelectOrganization prompts the user to select an organization
func SelectOrganization(cfg *config.Manager) (*config.Organization, error) {
	orgs := cfg.GetOrgs()

	if len(orgs) == 0 {
		return nil, fmt.Errorf("no organizations configured. Please run 'sprite org auth' first")
	}

	// Create options for existing organizations
	var options []huh.Option[string]
	for _, org := range orgs {
		displayName := format.GetOrgDisplayName(org.Name, org.URL)
		options = append(options, huh.NewOption(displayName, org.Name))
	}

	var selectedOrgKey string

	// Use individual field for inline rendering
	if err := huh.NewSelect[string]().
		Title("Which organization are you working with?").
		Description("Select an existing organization.").
		Options(options...).
		Height(15). // Maximum of 15 visible lines
		Value(&selectedOrgKey).
		Run(); err != nil {
		return nil, fmt.Errorf("organization selection cancelled: %w", err)
	}

	// Find the selected organization
	selectedOrg := orgs[selectedOrgKey]
	if selectedOrg == nil {
		return nil, fmt.Errorf("selected organization not found")
	}

	// Set as current org
	if err := cfg.SetCurrentOrg(selectedOrg.Name); err != nil {
		return nil, fmt.Errorf("failed to set current organization: %w", err)
	}

	displayName := format.GetOrgDisplayName(selectedOrg.Name, selectedOrg.URL)
	// Only show organization selection message in debug mode
	if slog.Default().Enabled(context.Background(), slog.LevelDebug) {
		fmt.Printf("\n%s Using organization: %s\n", format.Success("✓"), format.Org(displayName))
	}

	return selectedOrg, nil
}

// FlyOrganization represents a Fly.io organization
type FlyOrganization struct {
	ID     string
	Slug   string
	Name   string
	Type   string
	Status string
}

// PromptForFlyOrganization prompts the user to select a Fly.io organization
func PromptForFlyOrganization(orgs []FlyOrganization) (*FlyOrganization, error) {
	if len(orgs) == 0 {
		return nil, fmt.Errorf("no organizations found")
	}

	// Create options for organizations
	var options []huh.Option[string]
	orgMap := make(map[string]*FlyOrganization)

	for i := range orgs {
		org := &orgs[i]
		// Show more context in the option label for better inline experience
		label := org.Slug
		if org.Name != "" && org.Name != org.Slug {
			label = fmt.Sprintf("%s (%s)", org.Slug, org.Name)
		}
		options = append(options, huh.NewOption(label, org.Slug))
		orgMap[org.Slug] = org
	}

	var selectedSlug string

	// Use individual field for inline rendering
	if err := huh.NewSelect[string]().
		Title("Which Fly.io organization would you like to use?").
		Description("Select an organization to create a Sprite token for.").
		Options(options...).
		Height(15). // Maximum of 15 visible lines
		Value(&selectedSlug).
		Run(); err != nil {
		return nil, fmt.Errorf("organization selection cancelled: %w", err)
	}

	selectedOrg, exists := orgMap[selectedSlug]
	if !exists {
		return nil, fmt.Errorf("selected organization not found")
	}

	return selectedOrg, nil
}

// SelectURLForAlias prompts the user to select a URL for an unknown alias
func SelectURLForAlias(alias string, urls []string) (string, error) {
	if len(urls) == 0 {
		return "", fmt.Errorf("no URLs configured")
	}

	// Create options for URLs
	var options []huh.Option[string]
	for _, url := range urls {
		options = append(options, huh.NewOption(url, url))
	}

	var selectedURL string

	// Use individual field for inline rendering
	if err := huh.NewSelect[string]().
		Title(fmt.Sprintf("Unknown alias: %s", format.Bold(alias))).
		Description("This alias hasn't been used before. Which API URL should it point to?").
		Options(options...).
		Height(10). // Limit height for URL selection
		Value(&selectedURL).
		Run(); err != nil {
		return "", fmt.Errorf("URL selection cancelled: %w", err)
	}

	return selectedURL, nil
}
