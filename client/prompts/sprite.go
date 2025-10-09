package prompts

import (
	"fmt"
	"strings"

	"github.com/charmbracelet/huh"
)

// PromptForSpriteName prompts the user to enter a sprite name
func PromptForSpriteName() (string, error) {
	var spriteName string

	// Use individual field for inline rendering
	if err := huh.NewInput().
		Title("What would you like to name your sprite?").
		Description("Enter a name for your new sprite.").
		Placeholder("my-sprite").
		Value(&spriteName).
		Validate(func(s string) error {
			s = strings.TrimSpace(s)
			if s == "" {
				return fmt.Errorf("sprite name is required")
			}
			// Basic validation - alphanumeric, hyphens, underscores
			for _, c := range s {
				if !((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
					(c >= '0' && c <= '9') || c == '-' || c == '_') {
					return fmt.Errorf("sprite name can only contain letters, numbers, hyphens, and underscores")
				}
			}
			return nil
		}).
		Run(); err != nil {
		return "", fmt.Errorf("sprite name entry cancelled: %w", err)
	}

	return strings.TrimSpace(spriteName), nil
}

