package prompts

import (
	"context"
	"fmt"
	"log/slog"
	"os"
	"strings"

	"github.com/charmbracelet/huh"
	"github.com/superfly/sprite-env/client/config"
	"github.com/superfly/sprite-env/client/format"
)

// isInteractiveTerminal checks if we're running in an interactive terminal
func isInteractiveTerminal() bool {
	// Check if stdin is a terminal
	if fileInfo, _ := os.Stdin.Stat(); (fileInfo.Mode() & os.ModeCharDevice) == 0 {
		return false
	}

	// Check if stdout is a terminal
	if fileInfo, _ := os.Stdout.Stat(); (fileInfo.Mode() & os.ModeCharDevice) == 0 {
		return false
	}

	return true
}

// configureForm applies common accessibility and theming settings to a form
func configureForm(form *huh.Form) *huh.Form {
	// Enable accessible mode if explicitly requested or if not in interactive terminal
	accessibleMode := os.Getenv("ACCESSIBLE") != "" || !isInteractiveTerminal()
	form = form.WithAccessible(accessibleMode)

	// Apply NO_COLOR theme if requested
	if os.Getenv("NO_COLOR") != "" {
		form = form.WithTheme(huh.ThemeBase())
	}

	return form
}

// getOrgDisplayName returns a user-friendly display name for the organization
func getOrgDisplayName(org *config.Organization) string {
	return format.GetOrgDisplayName(org.Name, org.URL)
}

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

	form := huh.NewForm(
		huh.NewGroup(
			huh.NewSelect[string]().
				Key("org").
				Title("Which organization are you working with?").
				Description("Select an existing organization.").
				Options(options...).
				Value(&selectedOrgKey),
		),
	)

	// Configure form with accessibility and theming
	form = configureForm(form)

	if err := form.Run(); err != nil {
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

// PromptForSpriteName prompts the user to enter a sprite name
func PromptForSpriteName() (string, error) {
	var spriteName string

	form := huh.NewForm(
		huh.NewGroup(
			huh.NewInput().
				Key("sprite").
				Title("Which Sprite are you connecting to?").
				Description("Enter the name of the sprite you want to work with.").
				Placeholder("my-sprite").
				Value(&spriteName).
				Validate(func(s string) error {
					s = strings.TrimSpace(s)
					if s == "" {
						return fmt.Errorf("sprite name is required")
					}
					return nil
				}),
		),
	)

	// Configure form with accessibility and theming
	form = configureForm(form)

	if err := form.Run(); err != nil {
		return "", fmt.Errorf("sprite selection cancelled: %w", err)
	}

	return strings.TrimSpace(spriteName), nil
}

// PromptForConfirmation shows a confirmation dialog
func PromptForConfirmation(title, description string) (bool, error) {
	var confirmed bool

	form := huh.NewForm(
		huh.NewGroup(
			huh.NewConfirm().
				Key("confirm").
				Title(title).
				Description(description).
				Value(&confirmed).
				Affirmative("Yes").
				Negative("No"),
		),
	)

	// Configure form with accessibility and theming
	form = configureForm(form)

	if err := form.Run(); err != nil {
		return false, fmt.Errorf("confirmation cancelled: %w", err)
	}

	return confirmed, nil
}

// PromptForAuth prompts for organization authentication details
func PromptForAuth() (name, url, token string, err error) {
	form := huh.NewForm(
		huh.NewGroup(
			huh.NewNote().
				Title("🔧 Manual Organization Setup").
				Description("Enter the details for your organization manually."),

			huh.NewInput().
				Key("name").
				Title("Organization name").
				Description("A friendly name for this organization").
				Placeholder("my-org").
				Value(&name).
				Validate(func(s string) error {
					if strings.TrimSpace(s) == "" {
						return fmt.Errorf("organization name is required")
					}
					return nil
				}),

			huh.NewInput().
				Key("url").
				Title("API URL").
				Description("The base URL for your sprites API").
				Placeholder("https://api.example.com").
				Value(&url).
				Validate(func(s string) error {
					if strings.TrimSpace(s) == "" {
						return fmt.Errorf("API URL is required")
					}
					if !strings.HasPrefix(s, "http://") && !strings.HasPrefix(s, "https://") {
						return fmt.Errorf("API URL must start with http:// or https://")
					}
					return nil
				}),

			huh.NewInput().
				Key("token").
				Title("API Token").
				Description("Your authentication token for this API").
				Password(true).
				Value(&token).
				Validate(func(s string) error {
					if strings.TrimSpace(s) == "" {
						return fmt.Errorf("API token is required")
					}
					return nil
				}),
		),
	)

	// Configure form with accessibility and theming
	form = configureForm(form)

	if err := form.Run(); err != nil {
		return "", "", "", fmt.Errorf("authentication setup cancelled: %w", err)
	}

	return strings.TrimSpace(name), strings.TrimSpace(url), strings.TrimSpace(token), nil
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
		options = append(options, huh.NewOption(org.Slug, org.Slug))
		orgMap[org.Slug] = org
	}

	var selectedSlug string

	form := huh.NewForm(
		huh.NewGroup(
			huh.NewSelect[string]().
				Key("org").
				Title("Which Fly.io organization would you like to use?").
				Description("Select an organization to create a Sprite token for.").
				Options(options...).
				Value(&selectedSlug),
		),
	)

	// Configure form with accessibility and theming
	form = configureForm(form)

	if err := form.Run(); err != nil {
		return nil, fmt.Errorf("organization selection cancelled: %w", err)
	}

	selectedOrg, exists := orgMap[selectedSlug]
	if !exists {
		return nil, fmt.Errorf("selected organization not found")
	}

	return selectedOrg, nil
}

// PromptForInviteCode prompts the user to enter an invite code
func PromptForInviteCode() (string, error) {
	var inviteCode string

	form := huh.NewForm(
		huh.NewGroup(
			huh.NewInput().
				Key("invite_code").
				Title("Have you received an invite code for this org?").
				Description("Enter the invite code you received, or leave blank to cancel.").
				Placeholder("a1b2c3d4e5f6g7h8").
				Value(&inviteCode),
		),
	)

	// Configure form with accessibility and theming
	form = configureForm(form)

	if err := form.Run(); err != nil {
		return "", fmt.Errorf("invite code entry cancelled: %w", err)
	}

	inviteCode = strings.TrimSpace(inviteCode)
	if inviteCode == "" {
		return "", fmt.Errorf("no invite code provided")
	}

	return inviteCode, nil
}

// FlyOrganization represents a Fly.io organization
// This type is duplicated here to avoid circular import with commands package
type FlyOrganization struct {
	ID     string
	Slug   string
	Name   string
	Type   string
	Status string
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

	form := huh.NewForm(
		huh.NewGroup(
			huh.NewNote().
				Title(fmt.Sprintf("🔍 Unknown alias: %s", format.Bold(alias))).
				Description("This alias hasn't been used before. Which API URL should it point to?"),

			huh.NewSelect[string]().
				Key("url").
				Title("Select API URL").
				Description("Choose the API URL to associate with this alias.").
				Options(options...).
				Value(&selectedURL),
		),
	)

	// Configure form with accessibility and theming
	form = configureForm(form)

	if err := form.Run(); err != nil {
		return "", fmt.Errorf("URL selection cancelled: %w", err)
	}

	return selectedURL, nil
}
