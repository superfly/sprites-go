package prompts

import (
	"fmt"
	"strings"

	"github.com/charmbracelet/huh"
)

// PromptToAuthenticate shows a prompt asking if the user wants to authenticate
// Returns true if user wants to authenticate
func PromptToAuthenticate() (bool, error) {
	var confirmed bool

	if err := huh.NewConfirm().
		Title("Authentication Required").
		Description("You need to authenticate to continue. Start authentication flow?").
		Value(&confirmed).
		Affirmative("Yes, authenticate").
		Negative("No, cancel").
		Run(); err != nil {
		return false, fmt.Errorf("authentication prompt cancelled: %w", err)
	}

	return confirmed, nil
}

// PromptToReAuthenticate shows a prompt asking if the user wants to re-authenticate
func PromptToReAuthenticate(orgName string) (bool, error) {
	var confirmed bool

	title := fmt.Sprintf("No token found for organization: %s", orgName)

	if err := huh.NewConfirm().
		Title(title).
		Description("Would you like to re-authenticate this organization?").
		Value(&confirmed).
		Affirmative("Yes, re-authenticate").
		Negative("No, cancel").
		Run(); err != nil {
		return false, fmt.Errorf("re-authentication prompt cancelled: %w", err)
	}

	return confirmed, nil
}

// PromptForInviteCode prompts the user to enter an invite code
func PromptForInviteCode() (string, error) {
	var inviteCode string

	// Use individual field for inline rendering
	if err := huh.NewInput().
		Title("Have you received an invite code for this org?").
		Description("Enter the invite code you received, or leave blank to cancel.").
		Placeholder("a1b2c3d4e5f6g7h8").
		Value(&inviteCode).
		Run(); err != nil {
		return "", fmt.Errorf("invite code entry cancelled: %w", err)
	}

	inviteCode = strings.TrimSpace(inviteCode)
	if inviteCode == "" {
		return "", fmt.Errorf("no invite code provided")
	}

	return inviteCode, nil
}

// PromptForConfirmation shows a confirmation dialog
func PromptForConfirmation(title, description string) (bool, error) {
	var confirmed bool

	// Use individual field for inline rendering
	if err := huh.NewConfirm().
		Title(title).
		Description(description).
		Value(&confirmed).
		Affirmative("Yes").
		Negative("No").
		Run(); err != nil {
		return false, fmt.Errorf("confirmation cancelled: %w", err)
	}

	return confirmed, nil
}

// PromptForAuth prompts for organization authentication details (manual setup)
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
