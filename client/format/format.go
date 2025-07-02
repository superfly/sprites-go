package format

import (
	"fmt"
	"os"
	"strings"
)

// ANSI color codes
const (
	Reset   = "\033[0m"
	Bold    = "\033[1m"
	Red     = "\033[31m"
	Green   = "\033[32m"
	Yellow  = "\033[33m"
	Blue    = "\033[34m"
	Magenta = "\033[35m"
	Cyan    = "\033[36m"
	Gray    = "\033[90m"
	White   = "\033[97m"
)

// Check if we should use colors (not disabled, and terminal supports it)
func shouldUseColor() bool {
	// Check if explicitly disabled
	if os.Getenv("NO_COLOR") != "" {
		return false
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

// Org formats an organization name with consistent color (cyan)
func Org(name string) string {
	return colorize(name, Cyan)
}

// Sprite formats a sprite name with consistent color (green)
func Sprite(name string) string {
	return colorize(name, Green)
}

// Command formats a command with consistent color (yellow)
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