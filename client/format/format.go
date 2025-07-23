package format

import (
	"fmt"
	"os"
	"strings"

	"github.com/charmbracelet/lipgloss"
)

// ANSI color codes - using theme-adaptive colors
const (
	Reset = "\033[0m"
	Bold  = "\033[1m"

	// Basic colors that adapt to terminal themes
	Red     = "\033[91m" // Bright red - adapts better to dark/light themes
	Green   = "\033[92m" // Bright green - adapts better to dark/light themes
	Yellow  = "\033[93m" // Bright yellow - adapts better to dark/light themes
	Blue    = "\033[94m" // Bright blue - adapts better to dark/light themes
	Magenta = "\033[95m" // Bright magenta - adapts better to dark/light themes
	Cyan    = "\033[96m" // Bright cyan - adapts better to dark/light themes

	// Subtle colors for secondary information
	Gray = "\033[37m" // Light gray - works on both light and dark
	Dim  = "\033[2m"  // Dim text - lets terminal choose appropriate dimming
)

// Lipgloss adaptive colors for rich terminal UI components
var (
	// Core semantic colors for entities
	OrgColor     = lipgloss.AdaptiveColor{Light: "39", Dark: "87"}   // Cyan - for organizations
	SpriteColor  = lipgloss.AdaptiveColor{Light: "34", Dark: "82"}   // Green - for sprites
	CommandColor = lipgloss.AdaptiveColor{Light: "178", Dark: "220"} // Yellow - for commands

	// Status colors
	SuccessColor = lipgloss.AdaptiveColor{Light: "34", Dark: "82"}   // Green
	ErrorColor   = lipgloss.AdaptiveColor{Light: "124", Dark: "196"} // Red
	InfoColor    = lipgloss.AdaptiveColor{Light: "27", Dark: "117"}  // Blue
	WarningColor = lipgloss.AdaptiveColor{Light: "178", Dark: "220"} // Yellow

	// UI element colors
	BorderColor        = lipgloss.AdaptiveColor{Light: "240", Dark: "238"} // Subtle border
	HeaderColor        = lipgloss.AdaptiveColor{Light: "27", Dark: "117"}  // Blue accent for headers
	PrimaryTextColor   = lipgloss.AdaptiveColor{Light: "16", Dark: "255"}  // Main text
	SecondaryTextColor = lipgloss.AdaptiveColor{Light: "240", Dark: "245"} // Secondary/subtle text
	AccentColor        = lipgloss.AdaptiveColor{Light: "33", Dark: "87"}   // Accent color for highlights
)

// Check if we should use colors (not disabled, and terminal supports it)
func shouldUseColor() bool {
	// Check if explicitly disabled
	if os.Getenv("NO_COLOR") != "" {
		return false
	}

	// Check if FORCE_COLOR is set (useful for CI/testing)
	if os.Getenv("FORCE_COLOR") != "" {
		return true
	}

	// Check if stdout is a terminal
	if fileInfo, _ := os.Stdout.Stat(); (fileInfo.Mode() & os.ModeCharDevice) == 0 {
		return false
	}

	return true
}

// colorize returns the string with color codes if colors are enabled
func colorize(s string, color string) string {
	if !shouldUseColor() {
		return s
	}
	return color + s + Reset
}

// Org formats an organization name with consistent color (cyan - good contrast on both themes)
func Org(name string) string {
	return colorize(name, Cyan)
}

// Sprite formats a sprite name with consistent color (green - universally good)
func Sprite(name string) string {
	return colorize(name, Green)
}

// Command formats a command with consistent color (yellow - high visibility)
func Command(cmd string) string {
	return colorize(cmd, Yellow)
}

// Success formats success messages with green
func Success(msg string) string {
	return colorize(msg, Green)
}

// Error formats error messages with red
func Error(msg string) string {
	return colorize(msg, Red)
}

// Info formats info messages with blue
func Info(msg string) string {
	return colorize(msg, Blue)
}

// Context formats a context line showing org and action
func Context(org, action string) string {
	return fmt.Sprintf("%s: %s", Org(org), action)
}

// ContextSprite formats a context line showing org, action, and sprite
func ContextSprite(org, action, sprite string) string {
	return fmt.Sprintf("%s: %s %s", Org(org), action, Sprite(sprite))
}

// ContextCommand formats a context line for running a command
func ContextCommand(org, cmd, sprite string) string {
	cmdStr := Command(strings.Join(strings.Fields(cmd), " "))
	return fmt.Sprintf("%s: Running %s in sprite %s", Org(org), cmdStr, Sprite(sprite))
}

// Bold makes text bold
func BoldText(s string) string {
	return colorize(s, Bold)
}

// Question formats question prompts with blue
func Question(msg string) string {
	return colorize(msg, Blue)
}

// Subtle formats subtle text with dimmed appearance (theme-adaptive)
func Subtle(msg string) string {
	return colorize(msg, Dim)
}

// GetOrgDisplayName returns a user-friendly display name for the organization
func GetOrgDisplayName(name, url string) string {
	// For auto-generated names like "default-123456", just show the URL host
	if strings.HasPrefix(name, "default-") && url != "" {
		// Extract just the host part
		if strings.Contains(url, "api.machines.dev") {
			return "fly.io"
		}
		if strings.Contains(url, "api.sprites.dev") {
			return "sprites.dev"
		}
		// For other URLs, extract the domain
		parts := strings.Split(url, "//")
		if len(parts) > 1 {
			host := strings.Split(parts[1], "/")[0]
			host = strings.Split(host, ":")[0] // Remove port if present
			return host
		}
	}
	return name
}
