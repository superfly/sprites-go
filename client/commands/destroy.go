package commands

import (
	"context"
	"flag"
	"fmt"
	"os"
	"strings"

	"github.com/superfly/sprite-env/client/config"
	"github.com/superfly/sprite-env/client/format"
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

	// Get organization, client, and sprite using unified function
	org, _, sprite, err := GetOrgClientAndSprite(ctx, flags.Org, flags.Sprite)
	if err != nil {
		// Check if it's a cancellation error
		if strings.Contains(err.Error(), "cancelled") {
			handlePromptError(err)
		} else {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		}
		os.Exit(1)
	}

	if sprite.Name() == "" {
		fmt.Fprintf(os.Stderr, "Error: No sprite selected to destroy\n")
		os.Exit(1)
	}

	fmt.Println(format.Context(format.GetOrgDisplayName(org.Name, org.URL), fmt.Sprintf("About to destroy sprite %s", format.Sprite(sprite.Name()))))
	fmt.Println()

	if !*forceFlag {
		title := fmt.Sprintf("Destroy sprite %s?", sprite.Name())
		description := "⚠️  This will permanently destroy the sprite and all its data. This action cannot be undone."

		confirmed := PromptForConfirmationOrExit(title, description)

		if !confirmed {
			fmt.Println("Cancelled.")
			os.Exit(0)
		}
	}

	// Client is already created by GetOrgAndClient

	// Delete sprite using SDK
	ctxReq := context.Background()
	if err := sprite.Client().DeleteSprite(ctxReq, sprite.Name()); err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to destroy sprite: %v\n", err)
		os.Exit(1)
	}

	// Remove .sprite file if it exists and matches this sprite
	if spriteFile, _, _ := config.ReadSpriteFile(); spriteFile != nil {
		if spriteFile.Organization == org.Name && spriteFile.Sprite == sprite.Name() {
			if err := config.RemoveSpriteFile(); err != nil {
				fmt.Fprintf(os.Stderr, "Warning: Failed to remove .sprite file: %v\n", err)
			}
		}
	}

	fmt.Printf("\n%s Sprite %s destroyed successfully.\n", format.Success("✓"), format.Sprite(sprite.Name()))
}
