package commands

import (
	"context"
	"flag"
	"fmt"
	"log/slog"
	"os"
	"time"

	"github.com/charmbracelet/lipgloss"
	"github.com/charmbracelet/lipgloss/table"
	"github.com/superfly/sprite-env/client/config"
	"github.com/superfly/sprite-env/client/format"
	sprites "github.com/superfly/sprites-go"
	"golang.org/x/term"
)

// ListCommand handles the list command - lists all sprites
func ListCommand(ctx *GlobalContext, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "list",
		Usage:       "list [options]",
		Description: "List all sprites",
		FlagSet:     flag.NewFlagSet("list", flag.ContinueOnError),
		Examples: []string{
			"sprite list",
			"sprite list -o myorg",
			"sprite list --prefix dev",
		},
		Notes: []string{
			"Lists all sprites in the selected organization.",
			"Use --prefix to filter sprites by name prefix.",
		},
	}

	// Set up flags
	_ = NewSpriteFlags(cmd.FlagSet) // Register flags but we use ctx.OrgOverride instead
	var prefix string
	cmd.FlagSet.StringVar(&prefix, "prefix", "", "Filter sprites by name prefix")

	// Parse flags
	_, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	// Get organization and client using unified function
	org, client, err := GetOrgAndClient(ctx, ctx.OrgOverride)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}

	// List sprites with prefix filter if provided
	spriteList, err := ListSpritesWithClient(client, prefix)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error listing sprites: %v\n", err)
		os.Exit(1)
	}

	// Check if output is being piped
	if !term.IsTerminal(int(os.Stdout.Fd())) {
		// Just output names when piped
		for _, sprite := range spriteList {
			fmt.Println(sprite.Name())
		}
		return
	}

	// Display results
	if len(spriteList) == 0 {
		if prefix != "" {
			fmt.Printf("No sprites found with prefix '%s' in organization %s\n",
				prefix, format.Org(format.GetOrgDisplayName(org.Name, org.URL)))
		} else {
			fmt.Printf("No sprites found in organization %s\n",
				format.Org(format.GetOrgDisplayName(org.Name, org.URL)))
		}
		return
	}

	// Print header
	fmt.Printf("Sprites in organization %s:\n\n",
		format.Org(format.GetOrgDisplayName(org.Name, org.URL)))

	// Create table data
	rows := make([][]string, len(spriteList))
	for i, sprite := range spriteList {
		createdAgo := time.Since(sprite.CreatedAt)
		createdStr := formatDuration(createdAgo) + " ago"

		rows[i] = []string{
			sprite.Name(),
			createdStr,
		}
	}

	// Create table with lipgloss
	t := table.New().
		Headers("NAME", "CREATED").
		Rows(rows...).
		Border(lipgloss.NormalBorder()).
		BorderStyle(lipgloss.NewStyle().Foreground(format.BorderColor)).
		StyleFunc(func(row, col int) lipgloss.Style {
			// Headers are at row -1
			if row == -1 {
				return lipgloss.NewStyle().
					Bold(true).
					Foreground(format.HeaderColor).
					Align(lipgloss.Center)
			}

			// Data rows start at 0
			switch col {
			case 0: // Name column - sprite names should use SpriteColor
				return lipgloss.NewStyle().
					Foreground(format.SpriteColor)
			case 1: // Created column
				return lipgloss.NewStyle().
					Foreground(format.SecondaryTextColor).
					Align(lipgloss.Right)
			default:
				return lipgloss.NewStyle()
			}
		})

	fmt.Println(t)
	fmt.Printf("\nTotal: %d sprite(s)\n", len(spriteList))
}

// formatDuration formats a duration in a human-readable way
func formatDuration(d time.Duration) string {
	if d < time.Minute {
		return fmt.Sprintf("%ds", int(d.Seconds()))
	} else if d < time.Hour {
		return fmt.Sprintf("%dm", int(d.Minutes()))
	} else if d < 24*time.Hour {
		return fmt.Sprintf("%dh", int(d.Hours()))
	} else {
		days := int(d.Hours() / 24)
		if days == 1 {
			return "1 day"
		}
		return fmt.Sprintf("%d days", days)
	}
}

// ListSpritesWithClient fetches the list of sprites from the API with optional prefix filtering using an existing client
func ListSpritesWithClient(client *sprites.Client, prefix string) ([]*sprites.Sprite, error) {
	slog.Debug("Listing sprites", "prefix", prefix)

	// List sprites using SDK
	ctx := context.Background()
	spriteList, err := client.ListAllSprites(ctx, prefix)
	if err != nil {
		slog.Debug("Sprite list request failed", "error", err)
		return nil, fmt.Errorf("failed to list sprites: %w", err)
	}

	return spriteList, nil
}

// ListSpritesWithPrefix fetches the list of sprites from the API with optional prefix filtering
// This is kept for backward compatibility but should be replaced with ListSpritesWithClient
func ListSpritesWithPrefix(cfg *config.Manager, org *config.Organization, prefix string) ([]*sprites.Sprite, error) {
	// Get token
	token, err := org.GetToken()
	if err != nil {
		return nil, fmt.Errorf("failed to get auth token: %w", err)
	}

	// Create SDK client
	client := sprites.New(token, sprites.WithBaseURL(getSpritesAPIURL(org)))

	slog.Debug("Listing sprites",
		"url", getSpritesAPIURL(org),
		"org", org.Name,
		"prefix", prefix,
		"authorization", fmt.Sprintf("Bearer %s", truncateToken(token)))

	// List sprites using SDK
	ctx := context.Background()
	spriteList, err := client.ListAllSprites(ctx, prefix)
	if err != nil {
		slog.Debug("Sprite list request failed", "error", err)
		return nil, fmt.Errorf("failed to list sprites: %w", err)
	}

	return spriteList, nil
}

// ListSprites fetches the list of sprites from the API
func ListSprites(cfg *config.Manager, org *config.Organization) ([]*sprites.Sprite, error) {
	return ListSpritesWithPrefix(cfg, org, "")
}

// SyncSpritesWithConfig is now a no-op since we don't store sprites locally
func SyncSpritesWithConfig(cfg *config.Manager, org *config.Organization) error {
	// Sprites are no longer stored in local config
	// They are fetched from API when needed or passed through to API calls
	return nil
}
