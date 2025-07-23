package commands

import (
	"flag"
	"fmt"
	"io"
	"net/http"
	"os"
	"strings"

	"github.com/sprite-env/client/config"
	"github.com/sprite-env/client/format"
)

// DestroyCommand handles the destroy command
func DestroyCommand(ctx *GlobalContext, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "destroy",
		Usage:       "destroy [options]",
		Description: "Destroy the current sprite",
		FlagSet:     flag.NewFlagSet("destroy", flag.ContinueOnError),
		Examples: []string{
			"sprite destroy",
			"sprite destroy -o myorg -s mysprite",
			"sprite destroy --force",
		},
	}

	// Set up flags
	flags := NewSpriteFlags(cmd.FlagSet)
	forceFlag := cmd.FlagSet.Bool("force", false, "Skip confirmation prompt")

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	if len(remainingArgs) > 0 {
		fmt.Fprintf(os.Stderr, "Error: destroy takes no arguments\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	// Ensure we have an org and sprite
	org, spriteName, err := EnsureOrgAndSprite(ctx.ConfigMgr, flags.Org, flags.Sprite)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}

	if spriteName == "" {
		fmt.Fprintf(os.Stderr, "Error: No sprite selected to destroy\n")
		os.Exit(1)
	}

	fmt.Println(format.Context(format.GetOrgDisplayName(org.Name, org.URL), fmt.Sprintf("About to destroy sprite %s", format.Sprite(spriteName))))
	fmt.Println()

	if !*forceFlag {
		title := fmt.Sprintf("Destroy sprite %s?", spriteName)
		description := "⚠️  This will permanently destroy the sprite and all its data. This action cannot be undone."

		confirmed := PromptForConfirmationOrExit(title, description)

		if !confirmed {
			fmt.Println("Cancelled.")
			os.Exit(0)
		}
	}

	// Build the URL based on whether we're using the new API or backward compatibility
	var url string
	if org.Name != "env" && strings.Contains(getSpritesAPIURL(org), "sprites.dev") {
		// Use the new sprites API
		url = fmt.Sprintf("%s/v1/sprites/%s", getSpritesAPIURL(org), spriteName)
	} else {
		// Use direct endpoint for backward compatibility
		url = fmt.Sprintf("%s/sprite/destroy", org.URL)
	}

	httpReq, err := http.NewRequest("DELETE", url, nil)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create HTTP request: %v\n", err)
		os.Exit(1)
	}

	token, err := org.GetTokenWithKeyringDisabled(ctx.ConfigMgr.IsKeyringDisabled())
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to get auth token: %v\n", err)
		os.Exit(1)
	}
	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", token))

	client := &http.Client{}
	resp, err := client.Do(httpReq)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to make request: %v\n", err)
		os.Exit(1)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK && resp.StatusCode != http.StatusNoContent {
		body, _ := io.ReadAll(resp.Body)
		fmt.Fprintf(os.Stderr, "Error: Failed to destroy sprite (status %d): %s\n", resp.StatusCode, string(body))
		os.Exit(1)
	}

	// Remove .sprite file if it exists and matches this sprite
	if spriteFile, _, _ := config.ReadSpriteFile(); spriteFile != nil {
		if spriteFile.Organization == org.Name && spriteFile.Sprite == spriteName {
			if err := config.RemoveSpriteFile(); err != nil {
				fmt.Fprintf(os.Stderr, "Warning: Failed to remove .sprite file: %v\n", err)
			}
		}
	}

	fmt.Printf("\n%s Sprite %s destroyed successfully.\n", format.Success("✓"), format.Sprite(spriteName))
}
