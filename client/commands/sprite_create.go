package commands

import (
	"bytes"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"net/http"
	"os"
	"time"

	"github.com/sprite-env/client/config"
	"github.com/sprite-env/client/format"
	"github.com/sprite-env/client/prompts"
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
	flags := NewSpriteFlags(cmd.FlagSet)
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
	if flags.Org != "" {
		// Find the organization by name
		for _, o := range orgs {
			if o.Name == flags.Org {
				org = o
				break
			}
		}
		if org == nil {
			fmt.Fprintf(os.Stderr, "Error: Organization '%s' not found\n", flags.Org)
			os.Exit(1)
		}
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

	// Save .sprite file for convenience
	if err := config.WriteSpriteFile(org.Name, spriteName); err != nil {
		// Log but don't fail - .sprite file is a convenience feature
		if ctx.IsDebugEnabled() {
			fmt.Printf("Note: Failed to create .sprite file: %v\n", err)
		}
	} else if ctx.IsDebugEnabled() {
		fmt.Printf("Created .sprite file for %s:%s\n",
			format.Org(format.GetOrgDisplayName(org.Name, org.URL)),
			format.Sprite(spriteName))
	}
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
	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", token))
	httpReq.Header.Set("Content-Type", "application/json")

	// Make the request
	client := &http.Client{Timeout: 30 * time.Second}
	resp, err := client.Do(httpReq)
	if err != nil {
		return fmt.Errorf("failed to create sprite: %w", err)
	}
	defer resp.Body.Close()

	// Read response body
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return fmt.Errorf("failed to read response: %w", err)
	}

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
