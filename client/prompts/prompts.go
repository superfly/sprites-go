package prompts

import (
	"fmt"
	"os"
	"strings"

	"github.com/charmbracelet/huh"
	"github.com/sprite-env/client/config"
	"github.com/sprite-env/client/format"
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

// PromptForInitialLogin prompts the user to login when no organizations are configured
func PromptForInitialLogin(cfg *config.Manager) (*config.Organization, error) {
	var token string
	var useKeyring bool

	// Check if keyring is disabled
	keyringDisabled := cfg.IsKeyringDisabled()

	form := huh.NewForm(
		huh.NewGroup(
			huh.NewNote().
				Title("🔐 Authentication Required").
				Description("We need an API token to work with Sprites. You can get one from your dashboard."),

			huh.NewInput().
				Key("token").
				Title("Enter your API token").
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

	// Add keyring option only if keyring is available
	if !keyringDisabled {
		form = huh.NewForm(
			huh.NewGroup(
				huh.NewNote().
					Title("🔐 Authentication Required").
					Description("We need an API token to work with Sprites. You can get one from your dashboard."),

				huh.NewInput().
					Key("token").
					Title("Enter your API token").
					Password(true).
					Value(&token).
					Validate(func(s string) error {
						if strings.TrimSpace(s) == "" {
							return fmt.Errorf("API token is required")
						}
						return nil
					}),

				huh.NewConfirm().
					Key("keyring").
					Title("Store token securely in system keyring?").
					Description("Recommended for security. Choose 'No' to store in config file.").
					Value(&useKeyring).
					Affirmative("Yes").
					Negative("No"),
			),
		)
	}

	// Configure form with accessibility and theming
	form = configureForm(form)

	if err := form.Run(); err != nil {
		return nil, fmt.Errorf("authentication cancelled: %w", err)
	}

	// Use the Sprites API URL (can be overridden with SPRITES_API_URL)
	url := "https://api.sprites.dev"
	if envURL := os.Getenv("SPRITES_API_URL"); envURL != "" {
		url = envURL
	}

	// Show validation progress
	fmt.Print("Validating token...")
	orgInfo, err := fetchOrganizationInfo(token, url)
	if err != nil {
		fmt.Print("\r\033[K") // Clear the line
		return nil, fmt.Errorf("token validation failed: %w", err)
	}
	fmt.Print("\r\033[K") // Clear the line

	// Use the organization name from API
	orgName := orgInfo.Organization

	// Temporarily disable keyring if user chose not to use it
	if !keyringDisabled && !useKeyring {
		cfg.SetKeyringDisabled(true)
	}

	// Add the organization
	if err := cfg.AddOrg(orgName, token, url); err != nil {
		// Restore keyring setting if we changed it
		if !keyringDisabled && !useKeyring {
			cfg.SetKeyringDisabled(false)
		}
		return nil, fmt.Errorf("failed to save credentials: %w", err)
	}

	// Restore keyring setting if we changed it
	if !keyringDisabled && !useKeyring {
		cfg.SetKeyringDisabled(false)
	}

	fmt.Println(format.Success("✓ Authenticated with organization: " + format.Org(orgName)))
	fmt.Println(format.Success("✓ Ready to work with Sprites!") + "\n")

	// Return the newly added org
	return cfg.GetOrgs()[orgName], nil
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

	// Add option to add new organization
	options = append(options, huh.NewOption("🔗 Add new organization", "__add_new__"))

	var selectedOrgKey string

	form := huh.NewForm(
		huh.NewGroup(
			huh.NewSelect[string]().
				Key("org").
				Title("Which organization are you working with?").
				Description("Select an existing organization or add a new one.").
				Options(options...).
				Value(&selectedOrgKey),
		),
	)

	// Configure form with accessibility and theming
	form = configureForm(form)

	if err := form.Run(); err != nil {
		return nil, fmt.Errorf("organization selection cancelled: %w", err)
	}

	// Check if user wants to add a new organization
	if selectedOrgKey == "__add_new__" {
		fmt.Println()
		newOrg, err := PromptForInitialLogin(cfg)
		if err != nil {
			return nil, fmt.Errorf("failed to add new organization: %w", err)
		}
		return newOrg, nil
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
	fmt.Printf("\n%s Using organization: %s\n", format.Success("✓"), format.Org(displayName))

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
