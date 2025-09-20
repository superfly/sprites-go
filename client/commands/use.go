package commands

import (
	"flag"
	"fmt"
	"os"
	"strings"

	"github.com/charmbracelet/huh"
	"github.com/superfly/sprite-env/client/config"
	"github.com/superfly/sprite-env/client/format"
	"github.com/superfly/sprite-env/client/prompts"
)

// UseCommand handles the use command - creates a .sprite file to activate a sprite in the current directory
func UseCommand(ctx *GlobalContext, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "use",
		Usage:       "use [options] [sprite-name]",
		Description: "Activate a sprite for the current directory",
		FlagSet:     flag.NewFlagSet("use", flag.ContinueOnError),
		Examples: []string{
			"sprite use my-sprite",
			"sprite use -o myorg dev-sprite",
			"sprite use", // Interactive mode
		},
		Notes: []string{
			"Creates a .sprite file in the current directory to set the active sprite.",
			"This file will be used by other commands when no sprite is explicitly specified.",
			"Similar to 'nvm use' or 'asdf local' for version management.",
			"If no sprite name is provided, shows an interactive list to choose from.",
		},
	}

	// Set up flags
	flags := NewSpriteFlags(cmd.FlagSet)
	var remove bool
	cmd.FlagSet.BoolVar(&remove, "unset", false, "Remove the .sprite file from the current directory")

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	// Handle unset flag
	if remove {
		if err := config.RemoveSpriteFile(); err != nil {
			if os.IsNotExist(err) {
				fmt.Fprintf(os.Stderr, "No .sprite file found in the current directory\n")
			} else {
				fmt.Fprintf(os.Stderr, "Error removing .sprite file: %v\n", err)
			}
			os.Exit(1)
		}
		fmt.Printf("%s Removed .sprite file from current directory\n", format.Success("✓"))
		return
	}

	// Get sprite name from arguments or flags
	var spriteName string
	if len(remainingArgs) > 0 {
		spriteName = remainingArgs[0]
	} else if flags.Sprite != "" {
		spriteName = flags.Sprite
	}

	// Ensure we have an organization
	orgs := ctx.ConfigMgr.GetOrgs()
	if len(orgs) == 0 {
		fmt.Fprintf(os.Stderr, "Error: No organizations configured. Please run 'sprite org auth' first.\n")
		os.Exit(1)
	}

	// Get the organization (use override if provided)
	var org *config.Organization
	if flags.Org != "" {
		// Try to find the organization with alias support
		foundOrg, foundURL, err := ctx.ConfigMgr.FindOrgWithAlias(flags.Org)
		if err != nil {
			// Check if it's an unknown alias error
			if strings.Contains(err.Error(), "unknown alias:") {
				// Parse the org specification to get the alias
				_, alias, _ := ctx.ConfigMgr.ParseOrgWithAlias(flags.Org)

				// Get all available URLs
				urls := ctx.ConfigMgr.GetAllURLs()
				if len(urls) > 0 {
					// Prompt user to select a URL for this alias
					selectedURL, promptErr := prompts.SelectURLForAlias(alias, urls)
					if promptErr != nil {
						fmt.Fprintf(os.Stderr, "Error: Failed to select URL for alias: %v\n", promptErr)
						os.Exit(1)
					}

					// Save the alias
					if saveErr := ctx.ConfigMgr.SetURLAlias(alias, selectedURL); saveErr != nil {
						fmt.Fprintf(os.Stderr, "Error: Failed to save alias: %v\n", saveErr)
						os.Exit(1)
					}

					fmt.Printf("%s Saved alias '%s' for URL %s\n",
						format.Success("✓"),
						format.Bold(alias),
						format.URL(selectedURL))

					// Try again with the newly saved alias
					foundOrg, foundURL, err = ctx.ConfigMgr.FindOrgWithAlias(flags.Org)
					if err != nil {
						fmt.Fprintf(os.Stderr, "Error: %v\n", err)
						os.Exit(1)
					}
				} else {
					fmt.Fprintf(os.Stderr, "Error: No URLs configured to associate with alias '%s'\n", alias)
					os.Exit(1)
				}
			} else {
				fmt.Fprintf(os.Stderr, "Error: %v\n", err)
				os.Exit(1)
			}
		}
		org = foundOrg
		_ = foundURL // silence unused variable warning
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

	// If no sprite name provided, show interactive list
	if spriteName == "" {
		sprites, err := ListSprites(ctx.ConfigMgr, org)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error listing sprites: %v\n", err)
			os.Exit(1)
		}

		if len(sprites) == 0 {
			fmt.Fprintf(os.Stderr, "No sprites found in organization %s\n",
				format.Org(format.GetOrgDisplayName(org.Name, org.URL)))
			os.Exit(1)
		}

		// Create options for sprite selection
		options := make([]huh.Option[string], len(sprites))
		for i, sprite := range sprites {
			label := fmt.Sprintf("%s (%s)", sprite.Name, sprite.Status)
			options[i] = huh.NewOption(label, sprite.Name)
		}

		// Prompt user to select a sprite
		err = huh.NewSelect[string]().
			Title("Select a sprite").
			Options(options...).
			Value(&spriteName).
			Run()

		if err != nil {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
			os.Exit(1)
		}
	}

	// Create .sprite file
	if err := config.WriteSpriteFile(org.Name, spriteName); err != nil {
		fmt.Fprintf(os.Stderr, "Error creating .sprite file: %v\n", err)
		os.Exit(1)
	}

	fmt.Printf("%s Now using sprite %s from organization %s\n",
		format.Success("✓"),
		format.Sprite(spriteName),
		format.Org(format.GetOrgDisplayName(org.Name, org.URL)))
	fmt.Printf("\nOther commands in this directory will use this sprite by default.\n")
	fmt.Printf("To unset, run: %s\n", format.Command("sprite use --unset"))
}
