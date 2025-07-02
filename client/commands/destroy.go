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
func DestroyCommand(cfg *config.Manager, args []string) {
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
	force := cmd.FlagSet.Bool("force", false, "Skip confirmation prompt")

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
	org, sprite, isNewSprite, err := EnsureOrgAndSprite(cfg, flags.Org, flags.Sprite)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}

	// Destroy should always fail for new sprites since they don't exist on the server yet
	if isNewSprite {
		fmt.Fprintf(os.Stderr, "Error: Cannot destroy a sprite that hasn't been created yet\n")
		os.Exit(1)
	}

	if sprite == nil {
		fmt.Fprintf(os.Stderr, "Error: No sprite selected to destroy\n")
		os.Exit(1)
	}

	fmt.Println(format.Context(format.GetOrgDisplayName(org.Name, org.URL), fmt.Sprintf("About to destroy sprite %s", format.Sprite(sprite.Name))))
	fmt.Println()

	if !*force {
		fmt.Printf("Warning: This will permanently destroy sprite %s\n", format.Sprite(sprite.Name))
		fmt.Print("Are you sure? (y/N): ")

		var response string
		fmt.Scanln(&response)

		if response != "y" && response != "Y" {
			fmt.Println("Destroy cancelled.")
			os.Exit(0)
		}
	}

	// Build the URL based on whether we're using the new API or backward compatibility
	var url string
	if org.Name != "env" && strings.Contains(getSpritesAPIURL(org), "sprites.dev") {
		// Use the new sprites API
		url = fmt.Sprintf("%s/v1/sprites/%s", getSpritesAPIURL(org), sprite.Name)
	} else {
		// Use direct endpoint for backward compatibility
		url = fmt.Sprintf("%s/sprite/destroy", org.URL)
	}

	httpReq, err := http.NewRequest("DELETE", url, nil)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create HTTP request: %v\n", err)
		os.Exit(1)
	}

	token, err := org.GetToken()
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

	// Remove sprite from local config
	if err := cfg.RemoveSprite(sprite.Name); err != nil {
		fmt.Fprintf(os.Stderr, "Warning: Failed to remove sprite from local config: %v\n", err)
	}

	// Remove .sprite file if it exists and matches this sprite
	if spriteFile, _ := config.ReadSpriteFile(); spriteFile != nil {
		if spriteFile.Organization == org.Name && spriteFile.Sprite == sprite.Name {
			if err := config.RemoveSpriteFile(); err != nil {
				fmt.Fprintf(os.Stderr, "Warning: Failed to remove .sprite file: %v\n", err)
			}
		}
	}

	fmt.Printf("\n%s Sprite %s destroyed successfully.\n", format.Success("✓"), format.Sprite(sprite.Name))
}
