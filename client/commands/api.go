package commands

import (
	"flag"
	"fmt"
	"os"
	"os/exec"
	"strings"

	"github.com/sprite-env/client/format"
)

// ApiCommand makes authenticated API calls using curl
func ApiCommand(ctx *GlobalContext, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "api",
		Usage:       "api [options] <path> [curl options]",
		Description: "Make authenticated API calls with curl",
		FlagSet:     flag.NewFlagSet("api", flag.ContinueOnError),
		Examples: []string{
			"sprite api -o myorg -s my-sprite /upgrade -X POST",
			"sprite api -o myorg -s my-sprite /exec -X GET",
			"sprite api -o myorg -s my-sprite /checkpoints",
		},
		Notes: []string{
			"This command wraps curl to automatically add authentication headers.",
			"The path is relative to /v1/sprites/<sprite-name>/",
			"All arguments after the path are passed directly to curl.",
		},
	}

	// Set up flags
	flags := NewSpriteFlags(cmd.FlagSet)

	// Custom error handling to stop parsing after first non-flag
	cmd.FlagSet.Usage = func() {
		fmt.Fprintf(os.Stderr, "%s\n\n", cmd.Description)
		fmt.Fprintf(os.Stderr, "Usage:\n  sprite %s\n\n", cmd.Usage)
		fmt.Fprintf(os.Stderr, "Options:\n")
		cmd.FlagSet.PrintDefaults()
		fmt.Fprintln(os.Stderr)
		if len(cmd.Examples) > 0 {
			fmt.Fprintf(os.Stderr, "Examples:\n")
			for _, example := range cmd.Examples {
				fmt.Fprintf(os.Stderr, "  %s\n", example)
			}
			fmt.Fprintln(os.Stderr)
		}
		if len(cmd.Notes) > 0 {
			fmt.Fprintf(os.Stderr, "Notes:\n")
			for _, note := range cmd.Notes {
				fmt.Fprintf(os.Stderr, "  %s\n", note)
			}
			fmt.Fprintln(os.Stderr)
		}
	}

	// Check for help flags first
	for _, arg := range args {
		if arg == "-h" || arg == "--help" || arg == "-help" {
			cmd.FlagSet.Usage()
			os.Exit(0)
		}
	}

	// Parse only the flags we know about (up to the path)
	var remainingArgs []string
	i := 0
	for i < len(args) {
		arg := args[i]

		// Stop if we hit "--" (standard flag terminator)
		if arg == "--" {
			remainingArgs = args[i+1:]
			args = args[:i]
			break
		}

		// If it's a flag, check if it needs a value
		if strings.HasPrefix(arg, "-") {
			// Check if this is a known flag that needs a value
			needsValue := false
			flagName := strings.TrimLeft(arg, "-")

			// Handle both -flag=value and -flag value formats
			if strings.Contains(flagName, "=") {
				// Flag has embedded value, just continue
				i++
				continue
			}

			// Check if this flag needs a value
			switch flagName {
			case "o", "org", "s", "sprite":
				needsValue = true
			case "debug", "h", "help":
				needsValue = false
			default:
				// Unknown flag, assume it's for curl
				remainingArgs = args[i:]
				args = args[:i]
				break
			}

			if needsValue && i+1 < len(args) && !strings.HasPrefix(args[i+1], "-") {
				// Skip the value
				i += 2
			} else {
				i++
			}
		} else {
			// Non-flag argument (the path)
			remainingArgs = args[i:]
			args = args[:i]
			break
		}
	}

	// Parse the flags
	if err := cmd.FlagSet.Parse(args); err != nil {
		if err == flag.ErrHelp {
			os.Exit(0)
		}
		fmt.Fprintf(os.Stderr, "Error: %v\n\n", err)
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	// Check for path argument
	if len(remainingArgs) < 1 {
		fmt.Fprintf(os.Stderr, "Error: api requires a path argument\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	path := remainingArgs[0]
	curlArgs := remainingArgs[1:]

	// Ensure we have org and sprite
	org, spriteName, err := EnsureOrgAndSprite(ctx.ConfigMgr, flags.Org, flags.Sprite)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}

	if spriteName == "" {
		fmt.Fprintf(os.Stderr, "Error: sprite name is required. Use -s flag or set it via .sprite file\n")
		os.Exit(1)
	}

	// Get auth token
	token, err := org.GetTokenWithKeyringDisabled(ctx.ConfigMgr.IsKeyringDisabled())
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to get auth token: %v\n", err)
		os.Exit(1)
	}

	// Build the full URL
	baseURL := getSpritesAPIURL(org)

	// Clean up the path
	if !strings.HasPrefix(path, "/") {
		path = "/" + path
	}

	fullURL := baseURL + "/v1/sprites/" + spriteName + path

	// Check if curl is installed
	curlPath, err := exec.LookPath("curl")
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: curl is not installed. Please install curl to use this command.\n")
		os.Exit(1)
	}

	// Build curl command
	curlCmd := []string{
		curlPath,
		"-H", fmt.Sprintf("Authorization: Bearer %s", token),
		fullURL,
	}

	// Add any additional curl arguments
	curlCmd = append(curlCmd, curlArgs...)

	// Show what we're doing
	fmt.Printf("Calling API: %s %s\n",
		format.Org(format.GetOrgDisplayName(org.Name, org.URL)),
		format.Sprite(spriteName))
	fmt.Printf("URL: %s\n\n", fullURL)

	// Execute curl
	execCmd := exec.Command(curlCmd[0], curlCmd[1:]...)
	execCmd.Stdin = os.Stdin
	execCmd.Stdout = os.Stdout
	execCmd.Stderr = os.Stderr

	if err := execCmd.Run(); err != nil {
		// curl will have printed its own error message
		if exitErr, ok := err.(*exec.ExitError); ok {
			os.Exit(exitErr.ExitCode())
		}
		os.Exit(1)
	}
}
