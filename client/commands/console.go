package commands

import (
	"flag"
	"fmt"
	"os"
)

// ConsoleCommand handles the console command - opens an interactive shell
func ConsoleCommand(ctx *GlobalContext, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "console",
		Usage:       "console [options]",
		Description: "Open an interactive shell in the sprite environment",
		FlagSet:     flag.NewFlagSet("console", flag.ContinueOnError),
		Examples: []string{
			"sprite console",
			"sprite console -o myorg -s mysprite",
		},
		Notes: []string{
			"This is a shortcut for: sprite exec -tty /bin/bash --login",
			"Opens an interactive bash shell with a TTY allocated",
		},
	}

	// Set up sprite flags (org/sprite selection)
	flags := NewSpriteFlags(cmd.FlagSet)

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	// Console command doesn't take any additional arguments
	if len(remainingArgs) > 0 {
		fmt.Fprintf(os.Stderr, "Error: console command takes no arguments\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	// Build the exec command arguments
	execArgs := []string{"-tty", "/bin/bash", "--login"}

	// If org/sprite were specified, pass them through
	if flags.Org != "" {
		execArgs = append([]string{"-org", flags.Org}, execArgs...)
	}
	if flags.Sprite != "" {
		execArgs = append([]string{"-sprite", flags.Sprite}, execArgs...)
	}

	// Call ExecCommand with the constructed arguments
	ExecCommand(ctx, execArgs)
}
