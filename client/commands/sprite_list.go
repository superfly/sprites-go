package commands

import (
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"net/url"
	"os"
	"strings"
	"time"

	"github.com/charmbracelet/lipgloss"
	"github.com/charmbracelet/lipgloss/table"
	"github.com/superfly/sprite-env/client/config"
	"github.com/superfly/sprite-env/client/format"
	"github.com/superfly/sprite-env/client/prompts"
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

	// Ensure we have an organization
	orgs := ctx.ConfigMgr.GetOrgs()
	if len(orgs) == 0 {
		fmt.Fprintf(os.Stderr, "Error: No organizations configured. Please run 'sprite org auth' first.\n")
		os.Exit(1)
	}

	// Get the organization (use override if provided)
	var org *config.Organization
	orgOverride := ctx.OrgOverride // Use the global context's org override
	slog.Debug("Getting organization", "ctx.OrgOverride", ctx.OrgOverride)
	if orgOverride != "" {
		slog.Debug("Using org override with alias support", "orgSpec", orgOverride)
		// Try to find the organization with alias support
		foundOrg, _, err := ctx.ConfigMgr.FindOrgWithAlias(orgOverride)
		if err != nil {
			// Check if it's an unknown alias error
			if strings.Contains(err.Error(), "unknown alias:") {
				// Parse the org specification to get the alias
				_, alias, _ := ctx.ConfigMgr.ParseOrgWithAlias(orgOverride)

				// Get all configured URLs
				urls := ctx.ConfigMgr.GetAllURLs()
				if len(urls) == 0 {
					fmt.Fprintf(os.Stderr, "Error: No URLs configured\n")
					os.Exit(1)
				}

				// Prompt user to select URL for this alias
				selectedURL, err := prompts.SelectURLForAlias(alias, urls)
				if err != nil {
					fmt.Fprintf(os.Stderr, "Error: %v\n", err)
					os.Exit(1)
				}

				// Save the alias
				if err := ctx.ConfigMgr.SetURLAlias(alias, selectedURL); err != nil {
					fmt.Fprintf(os.Stderr, "Error: Failed to save alias: %v\n", err)
					os.Exit(1)
				}
				fmt.Printf("✓ Saved alias '%s' for URL %s\n", alias, format.URL(selectedURL))

				// Try again with the saved alias
				foundOrg, _, err = ctx.ConfigMgr.FindOrgWithAlias(orgOverride)
				if err != nil {
					fmt.Fprintf(os.Stderr, "Error: %v\n", err)
					os.Exit(1)
				}
			} else {
				fmt.Fprintf(os.Stderr, "Error: %v\n", err)
				os.Exit(1)
			}
		}
		org = foundOrg
		slog.Debug("Found organization with alias", "org", org.Name, "url", org.URL)
	} else {
		// Use current org or first available
		org = ctx.ConfigMgr.GetCurrentOrg()
		if org == nil && len(orgs) > 0 {
			// Get the first org from the map
			for _, o := range orgs {
				org = o
				break
			}
		}
		if org == nil {
			fmt.Fprintf(os.Stderr, "Error: No organization selected\n")
			os.Exit(1)
		}
	}

	// List sprites with prefix filter if provided
	sprites, err := ListSpritesWithPrefix(ctx.ConfigMgr, org, prefix)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error listing sprites: %v\n", err)
		os.Exit(1)
	}

	// Check if output is being piped
	if !term.IsTerminal(int(os.Stdout.Fd())) {
		// Just output names when piped
		for _, sprite := range sprites {
			fmt.Println(sprite.Name)
		}
		return
	}

	// Display results
	if len(sprites) == 0 {
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
	rows := make([][]string, len(sprites))
	for i, sprite := range sprites {
		createdAgo := time.Since(sprite.CreatedAt)
		createdStr := formatDuration(createdAgo) + " ago"

		rows[i] = []string{
			sprite.Name,
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
	fmt.Printf("\nTotal: %d sprite(s)\n", len(sprites))
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

// SpritesListResponse represents the response from listing sprites
type SpritesListResponse struct {
	Sprites               []SpriteInfo `json:"sprites"`
	HasMore               bool         `json:"has_more"`
	NextContinuationToken string       `json:"next_continuation_token,omitempty"`
}

// ListSpritesWithPrefix fetches the list of sprites from the API with optional prefix filtering
func ListSpritesWithPrefix(cfg *config.Manager, org *config.Organization, prefix string) ([]SpriteInfo, error) {
	var allSprites []SpriteInfo
	continuationToken := ""

	for {
		// Build URL with query parameters
		baseURL := fmt.Sprintf("%s/v1/sprites", getSpritesAPIURL(org))
		u, err := url.Parse(baseURL)
		if err != nil {
			return nil, fmt.Errorf("failed to parse URL: %w", err)
		}

		q := u.Query()
		q.Set("max_results", "100")
		if continuationToken != "" {
			q.Set("continuation_token", continuationToken)
		}
		if prefix != "" {
			q.Set("prefix", prefix)
		}
		u.RawQuery = q.Encode()

		// Create request
		httpReq, err := http.NewRequest("GET", u.String(), nil)
		if err != nil {
			return nil, fmt.Errorf("failed to create request: %w", err)
		}

		token, err := org.GetTokenWithKeyringDisabled(cfg.IsKeyringDisabled())
		if err != nil {
			return nil, fmt.Errorf("failed to get auth token: %w", err)
		}
		httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", token))

		slog.Debug("Sprite list request",
			"url", u.String(),
			"org", org.Name,
			"prefix", prefix,
			"continuation_token", continuationToken,
			"authorization", fmt.Sprintf("Bearer %s", truncateToken(token)))

		// Make request
		client := &http.Client{Timeout: 30 * time.Second}
		resp, err := client.Do(httpReq)
		if err != nil {
			slog.Debug("Sprite list request failed", "error", err)
			return nil, fmt.Errorf("failed to list sprites: %w", err)
		}
		defer resp.Body.Close()

		// Read response
		body, err := io.ReadAll(resp.Body)
		if err != nil {
			return nil, fmt.Errorf("failed to read response: %w", err)
		}

		slog.Debug("Sprite list response",
			"status", resp.StatusCode,
			"body", string(body))

		// Check status
		if resp.StatusCode != http.StatusOK {
			return nil, fmt.Errorf("failed to list sprites (status %d): %s", resp.StatusCode, string(body))
		}

		// Parse response
		var listResp SpritesListResponse
		if err := json.Unmarshal(body, &listResp); err != nil {
			return nil, fmt.Errorf("failed to parse response: %w", err)
		}

		allSprites = append(allSprites, listResp.Sprites...)

		// Check if there are more results
		if !listResp.HasMore || listResp.NextContinuationToken == "" {
			break
		}

		continuationToken = listResp.NextContinuationToken
	}

	return allSprites, nil
}

// ListSprites fetches the list of sprites from the API
func ListSprites(cfg *config.Manager, org *config.Organization) ([]SpriteInfo, error) {
	return ListSpritesWithPrefix(cfg, org, "")
}

// SyncSpritesWithConfig is now a no-op since we don't store sprites locally
func SyncSpritesWithConfig(cfg *config.Manager, org *config.Organization) error {
	// Sprites are no longer stored in local config
	// They are fetched from API when needed or passed through to API calls
	return nil
}
