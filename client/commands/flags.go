package commands

import (
	"flag"
	"fmt"
	"os"
)

// GlobalFlags contains flags that apply to all commands
type GlobalFlags struct {
	Debug bool
	Help  bool
}

// SpriteFlags contains flags for sprite-related commands
type SpriteFlags struct {
	GlobalFlags
	Org    string
	Sprite string
}

// Command represents a subcommand with its own flag set
type Command struct {
	Name        string
	Usage       string
	Description string
	Examples    []string
	Notes       []string
	FlagSet     *flag.FlagSet
	Execute     func(args []string) error
}

// NewGlobalFlags creates a new GlobalFlags with flags registered
func NewGlobalFlags(fs *flag.FlagSet) *GlobalFlags {
	gf := &GlobalFlags{}
	// Debug flag is handled globally in main.go, not per-command
	fs.BoolVar(&gf.Help, "help", false, "Show help for this command")
	fs.BoolVar(&gf.Help, "h", false, "Show help for this command (shorthand)")
	return gf
}

// NewSpriteFlags creates a new SpriteFlags with flags registered
func NewSpriteFlags(fs *flag.FlagSet) *SpriteFlags {
	sf := &SpriteFlags{}
	sf.GlobalFlags = *NewGlobalFlags(fs)
	fs.StringVar(&sf.Org, "org", "", "Organization to use")
	fs.StringVar(&sf.Org, "o", "", "Organization to use (shorthand)")
	fs.StringVar(&sf.Sprite, "sprite", "", "Sprite to use")
	fs.StringVar(&sf.Sprite, "s", "", "Sprite to use (shorthand)")
	return sf
}

// ParseFlags parses flags and handles help
func ParseFlags(cmd *Command, args []string) ([]string, error) {
	// Set custom usage function
	cmd.FlagSet.Usage = func() {
		fmt.Fprintf(os.Stderr, "%s\n\n", cmd.Description)
		fmt.Fprintf(os.Stderr, "Usage:\n  sprite %s\n\n", cmd.Usage)
		if cmd.FlagSet.NFlag() > 0 {
			fmt.Fprintf(os.Stderr, "Options:\n")
			cmd.FlagSet.PrintDefaults()
			fmt.Fprintln(os.Stderr)
		}

		if len(cmd.Notes) > 0 {
			fmt.Fprintf(os.Stderr, "Notes:\n")
			for _, note := range cmd.Notes {
				fmt.Fprintf(os.Stderr, "  %s\n", note)
			}
			fmt.Fprintln(os.Stderr)
		}

		if len(cmd.Examples) > 0 {
			fmt.Fprintf(os.Stderr, "Examples:\n")
			for _, example := range cmd.Examples {
				fmt.Fprintf(os.Stderr, "  %s\n", example)
			}
			fmt.Fprintln(os.Stderr)
		}
	}

	if err := cmd.FlagSet.Parse(args); err != nil {
		return nil, err
	}

	// Check for help flag
	helpFlag := cmd.FlagSet.Lookup("help")
	if helpFlag != nil && helpFlag.Value.String() == "true" {
		cmd.FlagSet.Usage()
		os.Exit(0)
	}

	return cmd.FlagSet.Args(), nil
}
