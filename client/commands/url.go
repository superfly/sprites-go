package commands

import (
	"context"
	"flag"
	"fmt"
	"os"

	"github.com/superfly/sprite-env/client/format"
	sprites "github.com/superfly/sprites-go"
)

// UrlCommand handles the url command - shows sprite URL and manages URL settings
func UrlCommand(ctx *GlobalContext, args []string) {
	if len(args) == 0 {
		// No subcommand, show URL
		showURL(ctx)
		return
	}

	subcommand := args[0]
	subArgs := args[1:]

	switch subcommand {
	case "update":
		updateURL(ctx, subArgs)
	case "help", "-h", "--help":
		printURLUsage()
	default:
		fmt.Fprintf(os.Stderr, "Error: Unknown subcommand '%s'\n\n", subcommand)
		printURLUsage()
		os.Exit(1)
	}
}

// showURL displays the sprite's URL
func showURL(ctx *GlobalContext) {
	// Get organization and client using unified function
	org, client, err := GetOrgAndClient(ctx, ctx.OrgOverride)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}

	// Get sprite name
	spriteName, err := getSpriteName(ctx, ctx.SpriteOverride)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}

	// Get sprite info
	spriteCtx := context.Background()
	sprite, err := client.GetSpriteWithOrg(spriteCtx, spriteName, &sprites.OrganizationInfo{
		Name: org.Name,
		URL:  org.URL,
	})
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error getting sprite info: %v\n", err)
		os.Exit(1)
	}

	// Display URL
	if sprite.URL == "" {
		fmt.Printf("No URL available for sprite %s\n",
			format.Sprite(spriteName))
	} else {
		fmt.Printf("URL: %s\n", sprite.URL)

		// Show auth status if available
		if sprite.URLSettings != nil && sprite.URLSettings.Auth != "" {
			fmt.Printf("Auth: %s\n", sprite.URLSettings.Auth)
		} else {
			fmt.Printf("Auth: default (authenticated)\n")
		}
	}
}

// updateURL handles updating URL settings
func updateURL(ctx *GlobalContext, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "url update",
		Usage:       "url update [options]",
		Description: "Update URL authentication settings",
		FlagSet:     flag.NewFlagSet("url update", flag.ContinueOnError),
		Examples: []string{
			"sprite url update --auth public",
			"sprite url update --auth default",
		},
		Notes: []string{
			"Changes the authentication requirement for the sprite's URL.",
			"Use 'public' to make the URL accessible without authentication.",
			"Use 'default' to require authentication (default behavior).",
		},
	}

	// Set up flags
	_ = NewSpriteFlags(cmd.FlagSet) // Register flags but we use ctx.OrgOverride instead
	var auth string
	cmd.FlagSet.StringVar(&auth, "auth", "", "Authentication type: 'public' or 'default'")

	// Parse flags
	_, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	// Validate auth parameter
	if auth == "" {
		fmt.Fprintf(os.Stderr, "Error: --auth parameter is required\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	if auth != "public" && auth != "default" {
		fmt.Fprintf(os.Stderr, "Error: --auth must be 'public' or 'default', got '%s'\n\n", auth)
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	// Get organization and client using unified function
	_, client, err := GetOrgAndClient(ctx, ctx.OrgOverride)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}

	// Get sprite name
	spriteName, err := getSpriteName(ctx, ctx.SpriteOverride)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}

	// Create URL settings
	var settings *sprites.URLSettings
	if auth == "public" {
		settings = &sprites.URLSettings{
			Auth: "public",
		}
	} else {
		// For "default", we can either omit the field or set it to empty
		// Setting it to empty string should work
		settings = &sprites.URLSettings{
			Auth: "",
		}
	}

	// Update URL settings
	spriteCtx := context.Background()
	err = client.UpdateURLSettings(spriteCtx, spriteName, settings)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error updating URL settings: %v\n", err)
		os.Exit(1)
	}

	// Show success message
	fmt.Printf("Updated URL settings for sprite %s\n",
		format.Sprite(spriteName))
	fmt.Printf("Auth: %s\n", auth)
}

// printURLUsage prints the usage for the url command
func printURLUsage() {
	fmt.Fprintf(os.Stderr, `sprite url - Manage sprite URL settings

Usage:
  sprite url                    Show sprite URL
  sprite url update [options]   Update URL authentication settings

Subcommands:
  update                        Update URL authentication settings

Options for update:
  --auth <type>                 Authentication type: 'public' or 'default'

Examples:
  sprite url                    # Show current URL
  sprite url update --auth public    # Make URL public
  sprite url update --auth default   # Require authentication

Notes:
  - The URL allows access to your sprite's web interface
  - By default, URLs require authentication using your API token
  - Setting auth to 'public' makes the URL accessible without authentication
  - Setting auth to 'default' requires authentication (default behavior)
`)
}
