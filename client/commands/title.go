package commands

import (
	"fmt"
	"log/slog"
	"strings"
)

func sanitizeTitlePart(s string) string {
	// Remove control characters that could break the terminal title
	// Strip ESC, BEL, and string terminator sequences
	s = strings.ReplaceAll(s, "\x1b", "")
	s = strings.ReplaceAll(s, "\u001b", "")
	s = strings.ReplaceAll(s, "\a", "")
	s = strings.ReplaceAll(s, "\\", "")
	// Collapse whitespace
	return strings.TrimSpace(s)
}

func buildTitle(spriteName, sessionID, cmd string) string {
	name := sanitizeTitlePart(spriteName)
	id := sanitizeTitlePart(sessionID)
	c := sanitizeTitlePart(cmd)

	if name == "" {
		name = "sprite"
	}

	// Build title with available information
	if id != "" && c != "" {
		return fmt.Sprintf("%s@%s: %s", name, id, c)
	}
	if id != "" {
		// If we have a session ID but no command, just show name@id
		return fmt.Sprintf("%s@%s", name, id)
	}
	if c != "" {
		// If we have a command but no session ID, show name: command
		return fmt.Sprintf("%s: %s", name, c)
	}
	// When nothing else is available, just show sprite name
	return name
}

// setTerminalTitle updates the local terminal/tab title using OSC 0.
// ESC ] 0 ; <title> BEL
func setTerminalTitle(title string, logger *slog.Logger) {
	if title == "" {
		return
	}
	if logger != nil {
		logger.Debug("Setting terminal title", "title", title)
	}
	// Avoid trailing newline to not disrupt TTY
	fmt.Printf("\033]0;%s\007", title)
}
