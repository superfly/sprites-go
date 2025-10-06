package commands

import (
    "fmt"
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

    // Only include command when we have a session ID
    if id != "" && c != "" {
        return fmt.Sprintf("%s@%s: %s", name, id, c)
    }
    if id != "" {
        return fmt.Sprintf("%s@%s:", name, id)
    }
    // When no session ID is present, just show sprite name
    return fmt.Sprintf("%s:", name)
}

// setTerminalTitle updates the local terminal/tab title using OSC 0.
// ESC ] 0 ; <title> BEL
func setTerminalTitle(title string) {
    if title == "" {
        return
    }
    // Avoid trailing newline to not disrupt TTY
    fmt.Printf("\033]0;%s\007", title)
}
