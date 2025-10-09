package commands

import (
	"context"
	"flag"
	"fmt"
	"log/slog"
	"os"

	"github.com/superfly/sprite-env/client/config"
	"github.com/superfly/sprite-env/client/format"
	"github.com/superfly/sprite-env/client/prompts"
	sprites "github.com/superfly/sprites-go"
)

// CreateCommand handles the create command - creates a new sprite
func CreateCommand(ctx *GlobalContext, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "create",
		Usage:       "create [options] [sprite-name]",
		Description: "Create a new sprite",
		FlagSet:     flag.NewFlagSet("create", flag.ContinueOnError),
		Examples: []string{
			"sprite create my-sprite",
			"sprite create -o myorg development-sprite",
			"sprite create",
		},
		Notes: []string{
			"Creates a new sprite with the specified name.",
			"The sprite will be created in the selected organization.",
			"If sprite name is not provided, you will be prompted.",
		},
	}

	// Set up flags
	_ = NewSpriteFlags(cmd.FlagSet) // Register flags but we use ctx.OrgOverride instead

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	// Get sprite name from args or prompt
	var spriteName string
	if len(remainingArgs) == 1 {
		spriteName = remainingArgs[0]
	} else if len(remainingArgs) == 0 {
		// Prompt for sprite name using clean prompt component
		spriteName, err = prompts.PromptForSpriteName()
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
			os.Exit(1)
		}
	} else {
		fmt.Fprintf(os.Stderr, "Error: create takes at most one argument (sprite name)\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	// Ensure authenticated and get org/client
	// This will:
	// 1. Do login flow if necessary
	// 2. Show org selector if needed
	// 3. Return the selected org and client
	org, client, err := EnsureAuthenticated(ctx, ctx.OrgOverride)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}

	// Create the sprite
	fmt.Printf("Creating sprite %s in organization %s...\n",
		format.Sprite(spriteName),
		format.Org(format.GetOrgDisplayName(org.Name, org.URL)))

	if err := CreateSpriteWithClient(client, spriteName); err != nil {
		fmt.Fprintf(os.Stderr, "Error creating sprite: %v\n", err)
		os.Exit(1)
	}

	fmt.Printf("%s Sprite %s created successfully!\n", format.Success("✓"), format.Sprite(spriteName))
}

// CreateSpriteWithClient creates a new sprite on the server using an existing client
func CreateSpriteWithClient(client *sprites.Client, spriteName string) error {
	slog.Debug("Creating sprite", "sprite", spriteName)

	// Create sprite using SDK
	ctx := context.Background()
	_, err := client.CreateSprite(ctx, spriteName, nil)
	if err != nil {
		slog.Debug("Sprite create request failed", "error", err)
		return fmt.Errorf("failed to create sprite: %w", err)
	}

	return nil
}

// CreateSprite creates a new sprite on the server
// When the API call returns successfully, the sprite is ready to use
// This is kept for backward compatibility but should be replaced with CreateSpriteWithClient
func CreateSprite(cfg *config.Manager, org *config.Organization, spriteName string) error {
	// Get token
	token, err := org.GetToken()
	if err != nil {
		return fmt.Errorf("failed to get auth token: %w", err)
	}

	// Additional safety check for empty tokens
	if token == "" {
		return fmt.Errorf("auth token is empty for organization %s", org.Name)
	}

	// Create SDK client
	client := sprites.New(token, sprites.WithBaseURL(getSpritesAPIURL(org)))

	slog.Debug("Creating sprite",
		"url", getSpritesAPIURL(org),
		"org", org.Name,
		"sprite", spriteName,
		"authorization", fmt.Sprintf("Bearer %s", truncateToken(token)))

	// Create sprite using SDK
	ctx := context.Background()
	_, err = client.CreateSprite(ctx, spriteName, nil)
	if err != nil {
		slog.Debug("Sprite create request failed", "error", err)
		return fmt.Errorf("failed to create sprite: %w", err)
	}

	// Save to local config (we don't need the ID since we're not tracking sprites locally)
	if err := SaveSprite(cfg, spriteName, ""); err != nil {
		return fmt.Errorf("failed to save sprite to config: %w", err)
	}

	return nil
}
