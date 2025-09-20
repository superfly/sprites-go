package commands

import (
	"bytes"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"os"
	"strings"
	"time"

	"github.com/superfly/sprite-env/client/config"
	"github.com/superfly/sprite-env/client/format"
	"github.com/superfly/sprite-env/client/prompts"
)

// SpriteCreateRequest represents the request to create a sprite
type SpriteCreateRequest struct {
	Name        string            `json:"name"`
	Config      *SpriteConfig     `json:"config,omitempty"`
	Environment map[string]string `json:"environment,omitempty"`
}

// SpriteConfig represents sprite configuration
type SpriteConfig struct {
	RamMB     int    `json:"ram_mb,omitempty"`
	CPUs      int    `json:"cpus,omitempty"`
	Region    string `json:"region,omitempty"`
	StorageGB int    `json:"storage_gb,omitempty"`
}

// SpriteCreateResponse represents the response from sprite creation
type SpriteCreateResponse struct {
	Name string `json:"name"`
}

// SpriteInfo represents sprite information from the API
type SpriteInfo struct {
	ID            string            `json:"id"`
	Name          string            `json:"name"`
	Organization  string            `json:"organization"`
	Status        string            `json:"status"`
	Config        *SpriteConfig     `json:"config,omitempty"`
	Environment   map[string]string `json:"environment,omitempty"`
	CreatedAt     time.Time         `json:"created_at"`
	UpdatedAt     time.Time         `json:"updated_at"`
	BucketName    string            `json:"bucket_name,omitempty"`
	PrimaryRegion string            `json:"primary_region,omitempty"`
}

// CreateCommand handles the create command - creates a new sprite
func CreateCommand(ctx *GlobalContext, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "create",
		Usage:       "create [options] <sprite-name>",
		Description: "Create a new sprite",
		FlagSet:     flag.NewFlagSet("create", flag.ContinueOnError),
		Examples: []string{
			"sprite create my-sprite",
			"sprite create -o myorg development-sprite",
		},
		Notes: []string{
			"Creates a new sprite with the specified name.",
			"The sprite will be created in the selected organization.",
		},
	}

	// Set up flags
	_ = NewSpriteFlags(cmd.FlagSet) // Register flags but we use ctx.OrgOverride instead
	// Note: We only use the org flag, not the sprite flag, since we're creating a new sprite

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	// Check for sprite name argument
	if len(remainingArgs) != 1 {
		fmt.Fprintf(os.Stderr, "Error: create requires exactly one argument (sprite name)\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	spriteName := remainingArgs[0]

	// Ensure we have an organization
	orgs := ctx.ConfigMgr.GetOrgs()
	if len(orgs) == 0 {
		fmt.Fprintf(os.Stderr, "Error: No organizations configured. Please run 'sprite org auth' first.\n")
		os.Exit(1)
	}

	// Get the organization (use override if provided)
	var org *config.Organization
	orgOverride := ctx.OrgOverride // Use the global context's org override
	if orgOverride != "" {
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
	} else {
		// Use current org or prompt for one
		org = ctx.ConfigMgr.GetCurrentOrg()
		if org == nil {
			// If no current org, prompt for one
			selectedOrg, err := prompts.SelectOrganization(ctx.ConfigMgr)
			if err != nil {
				fmt.Fprintf(os.Stderr, "Error: %v\n", err)
				os.Exit(1)
			}
			org = selectedOrg
		}
	}

	// Create the sprite
	fmt.Printf("Creating sprite %s in organization %s...\n",
		format.Sprite(spriteName),
		format.Org(format.GetOrgDisplayName(org.Name, org.URL)))

	if err := CreateSprite(ctx.ConfigMgr, org, spriteName); err != nil {
		fmt.Fprintf(os.Stderr, "Error creating sprite: %v\n", err)
		os.Exit(1)
	}

	fmt.Printf("%s Sprite %s created successfully!\n", format.Success("✓"), format.Sprite(spriteName))
}

// CreateSprite creates a new sprite on the server
// When the API call returns successfully, the sprite is ready to use
func CreateSprite(cfg *config.Manager, org *config.Organization, spriteName string) error {
	// Create the request
	req := SpriteCreateRequest{
		Name: spriteName,
		// TODO: Add config and environment based on user preferences or defaults
	}

	jsonData, err := json.Marshal(req)
	if err != nil {
		return fmt.Errorf("failed to marshal request: %w", err)
	}

	// Build the URL
	url := fmt.Sprintf("%s/v1/sprites", getSpritesAPIURL(org))

	// Create HTTP request
	httpReq, err := http.NewRequest("POST", url, bytes.NewReader(jsonData))
	if err != nil {
		return fmt.Errorf("failed to create request: %w", err)
	}

	token, err := org.GetToken()
	if err != nil {
		return fmt.Errorf("failed to get auth token: %w", err)
	}

	// Additional safety check for empty tokens
	if token == "" {
		return fmt.Errorf("auth token is empty for organization %s", org.Name)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", token))
	httpReq.Header.Set("Content-Type", "application/json")

	slog.Debug("Sprite create request",
		"url", url,
		"org", org.Name,
		"sprite", spriteName,
		"authorization", fmt.Sprintf("Bearer %s", truncateToken(token)),
		"request_body", string(jsonData))

	// Make the request
	client := &http.Client{Timeout: 120 * time.Second}
	resp, err := client.Do(httpReq)
	if err != nil {
		slog.Debug("Sprite create request failed", "error", err)
		return fmt.Errorf("failed to create sprite: %w", err)
	}
	defer resp.Body.Close()

	// Read response body
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return fmt.Errorf("failed to read response: %w", err)
	}

	slog.Debug("Sprite create response",
		"status", resp.StatusCode,
		"body", string(body))

	// Check status code
	if resp.StatusCode != http.StatusCreated {
		return fmt.Errorf("failed to create sprite (status %d): %s", resp.StatusCode, string(body))
	}

	// Parse response
	var createResp SpriteCreateResponse
	if err := json.Unmarshal(body, &createResp); err != nil {
		return fmt.Errorf("failed to parse response: %w", err)
	}

	// Save to local config (we don't need the ID since we're not tracking sprites locally)
	if err := SaveSprite(cfg, spriteName, ""); err != nil {
		return fmt.Errorf("failed to save sprite to config: %w", err)
	}

	return nil
}
