package prompts

import (
	"os"

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

