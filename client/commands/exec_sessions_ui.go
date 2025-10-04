package commands

import (
	"fmt"
	"strings"
	"time"

	tea "github.com/charmbracelet/bubbletea"
	"github.com/charmbracelet/lipgloss"
	"github.com/superfly/sprite-env/client/config"
	"github.com/superfly/sprite-env/client/format"
	sprites "github.com/superfly/sprites-go"
)

// SessionItem represents a tmux session for the list
type SessionItem struct {
	ID             string
	Command        string
	Created        time.Time
	BytesPerSecond float64
	IsActive       bool
	LastActivity   *time.Time
}

// formatTimeAgo formats a duration into a human-readable "time ago" string
func formatTimeAgo(t time.Time) string {
	duration := time.Since(t)
	if duration < time.Minute {
		return fmt.Sprintf("%ds ago", int(duration.Seconds()))
	} else if duration < time.Hour {
		return fmt.Sprintf("%dm ago", int(duration.Minutes()))
	} else if duration < 24*time.Hour {
		return fmt.Sprintf("%dh ago", int(duration.Hours()))
	} else {
		return fmt.Sprintf("%dd ago", int(duration.Hours()/24))
	}
}

// formatActivityRate formats the activity rate for display
func formatActivityRate(bytesPerSec float64, isActive bool) string {
	// Don't show activity when status is Idle
	if !isActive {
		return "-"
	}

	if bytesPerSec > 0 {
		if bytesPerSec < 1024 {
			return fmt.Sprintf("%.0f B/s", bytesPerSec)
		} else if bytesPerSec < 1024*1024 {
			return fmt.Sprintf("%.1f KB/s", bytesPerSec/1024)
		} else {
			return fmt.Sprintf("%.1f MB/s", bytesPerSec/(1024*1024))
		}
	}
	return "Active"
}

// Style definitions
var (
	normalStyle = lipgloss.NewStyle().
			Foreground(lipgloss.Color("252"))

	selectedStyle = lipgloss.NewStyle().
			Foreground(lipgloss.Color("230")).
			Background(lipgloss.Color("62")).
			Bold(true)

	activeIndicatorStyle = lipgloss.NewStyle().
				Foreground(lipgloss.Color("82")).
				Bold(true)

	inactiveIndicatorStyle = lipgloss.NewStyle().
				Foreground(lipgloss.Color("246"))

	headerStyle = lipgloss.NewStyle().
			Foreground(lipgloss.Color("250")).
			Bold(true).
			Underline(true)

	helpStyle = lipgloss.NewStyle().
			Foreground(lipgloss.Color("241")).
			MarginTop(1)
)

// sessionSelectorModel is the bubbletea model for session selection
type sessionSelectorModel struct {
	sessions []SessionItem
	cursor   int
	selected *SessionItem
	quit     bool
}

func newSessionSelectorModel(sessions []SessionItem) sessionSelectorModel {
	return sessionSelectorModel{
		sessions: sessions,
		cursor:   0,
	}
}

func (m sessionSelectorModel) Init() tea.Cmd {
	return nil
}

func (m sessionSelectorModel) Update(msg tea.Msg) (tea.Model, tea.Cmd) {
	switch msg := msg.(type) {
	case tea.KeyMsg:
		switch msg.String() {
		case "ctrl+c", "q", "esc":
			m.quit = true
			return m, tea.Quit

		case "up", "k":
			if m.cursor > 0 {
				m.cursor--
			}

		case "down", "j":
			if m.cursor < len(m.sessions)-1 {
				m.cursor++
			}

		case "enter", " ":
			if m.cursor < len(m.sessions) {
				m.selected = &m.sessions[m.cursor]
				return m, tea.Quit
			}
		}
	}

	return m, nil
}

func (m sessionSelectorModel) View() string {
	var b strings.Builder

	// Header
	header := fmt.Sprintf("%-4s %-30s %-12s %-15s %-10s", "ID", "Command", "Started", "Activity", "Status")
	b.WriteString(headerStyle.Render(header) + "\n")

	// Sessions
	for i, session := range m.sessions {
		// Format each field
		idStr := fmt.Sprintf("%-4s", session.ID)

		cmdStr := session.Command
		if len(cmdStr) > 29 {
			cmdStr = cmdStr[:26] + "..."
		}
		cmdStr = fmt.Sprintf("%-30s", cmdStr)

		timeStr := fmt.Sprintf("%-12s", formatTimeAgo(session.Created))
		activityStr := fmt.Sprintf("%-15s", formatActivityRate(session.BytesPerSecond, session.IsActive))

		// Status indicator
		var statusStr string
		if session.IsActive {
			statusStr = activeIndicatorStyle.Render("● Active")
		} else {
			statusStr = inactiveIndicatorStyle.Render("○ Idle  ")
		}
		statusStr = fmt.Sprintf("%-10s", statusStr)

		// Combine fields
		line := fmt.Sprintf("%s %s %s %s %s", idStr, cmdStr, timeStr, activityStr, statusStr)

		// Apply style based on selection
		if i == m.cursor && !m.quit && m.selected == nil {
			// Only show the arrow if we're still selecting
			b.WriteString(selectedStyle.Render(" → "+line) + "\n")
		} else {
			b.WriteString(normalStyle.Render("   "+line) + "\n")
		}
	}

	// Help text - only show if we're still selecting
	if !m.quit && m.selected == nil {
		help := "↑/k up • ↓/j down • enter select • q/esc cancel"
		b.WriteString(helpStyle.Render(help))
	}

	return b.String()
}

// runSessionSelector runs the interactive session selector and returns the selected session ID
func runSessionSelector(sessions []SessionItem, org *config.Organization, sprite *sprites.Sprite) (string, error) {
	if len(sessions) == 0 {
		fmt.Println("No active tmux sessions found.")
		fmt.Println("\nTo create a new detachable session:")
		fmt.Println("  sprite exec -detachable /bin/bash")
		fmt.Println("  sprite exec -detachable <command>")
		return "", fmt.Errorf("no sessions available")
	}

	// Show connection info
	fmt.Println()
	if sprite.Name() != "" && org.Name != "env" {
		fmt.Printf("Connected to %s sprite %s\n",
			format.Org(format.GetOrgDisplayName(org.Name, org.URL)),
			format.Sprite(sprite.Name()))
	} else if sprite.Name() != "" {
		fmt.Printf("Connected to sprite %s\n", format.Sprite(sprite.Name()))
	}
	fmt.Println()

	model := newSessionSelectorModel(sessions)

	// Run without alt screen for inline display
	p := tea.NewProgram(model)
	finalModel, err := p.Run()
	if err != nil {
		return "", err
	}

	if m, ok := finalModel.(sessionSelectorModel); ok && m.selected != nil {
		// Just add a newline and show what was selected
		fmt.Println()
		fmt.Printf("Attaching to session %s...\n", format.Sprite(m.selected.ID))
		return m.selected.ID, nil
	}

	// User cancelled - just add a newline for cleaner output
	fmt.Println()
	return "", fmt.Errorf("no session selected")
}

// listSessionsNonInteractive displays sessions in a non-interactive table format
func listSessionsNonInteractive(sessions []SessionItem, org *config.Organization, sprite *sprites.Sprite) int {
	if len(sessions) == 0 {
		fmt.Println("No active tmux sessions found.")
		fmt.Println("\nTo create a new detachable session:")
		fmt.Println("  sprite exec -detachable /bin/bash")
		fmt.Println("  sprite exec -detachable <command>")
		return 0
	}

	// Print table header
	fmt.Printf("%-6s %-20s %-30s %-15s\n", "ID", "Command", "Started", "Activity")
	fmt.Printf("%-6s %-20s %-30s %-15s\n", "──", "───────", "───────", "────────")

	// Print each session
	for _, session := range sessions {
		// Format command - truncate if too long
		cmdStr := session.Command
		if len(cmdStr) > 19 {
			cmdStr = cmdStr[:16] + "..."
		}

		// Format time
		timeStr := formatTimeAgo(session.Created)

		// Format activity
		activityStr := formatActivityRate(session.BytesPerSecond, session.IsActive)

		fmt.Printf("%-6s %-20s %-30s %-15s\n", session.ID, cmdStr, timeStr, activityStr)
	}

	fmt.Println("\nTo attach to a session:")
	fmt.Println("  sprite exec -id <session_id>")
	fmt.Println("\nTo create a new detachable session:")
	fmt.Println("  sprite exec -detachable <command>")

	return 0
}
