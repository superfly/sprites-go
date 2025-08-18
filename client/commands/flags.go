package commands

import (
	"flag"
	"fmt"
	"os"
	"strings"
)

// GlobalFlags contains flags that apply to all commands
type GlobalFlags struct {
	Debug bool
	Help  bool
}

// SpriteFlags contains flags for sprite-related commands
type SpriteFlags struct {
	GlobalFlags
	Org       string
	Sprite    string
	DebugFile string
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

// ParseGlobalFlagsFromAnyPosition parses global flags from any position in the arguments
// and returns the cleaned arguments with global flags removed
func ParseGlobalFlagsFromAnyPosition(args []string) ([]string, *SpriteFlags, error) {
	flags := &SpriteFlags{}

	// Create a temporary flag set to parse global flags
	tempFlagSet := flag.NewFlagSet("temp", flag.ContinueOnError)
	tempFlagSet.StringVar(&flags.Org, "org", "", "Organization to use")
	tempFlagSet.StringVar(&flags.Org, "o", "", "Organization to use (shorthand)")
	tempFlagSet.StringVar(&flags.Sprite, "sprite", "", "Sprite to use")
	tempFlagSet.StringVar(&flags.Sprite, "s", "", "Sprite to use (shorthand)")
	tempFlagSet.StringVar(&flags.DebugFile, "debug", "", "Enable debug logging (use 'stdout' or '-' for console, or specify a file path)")
	tempFlagSet.BoolVar(&flags.Help, "help", false, "Show help")
	tempFlagSet.BoolVar(&flags.Help, "h", false, "Show help (shorthand)")

	// Parse flags from any position
	cleanedArgs := make([]string, 0, len(args))

	for i := 0; i < len(args); i++ {
		arg := args[i]

		// Check if this is a flag
		if strings.HasPrefix(arg, "-") {
			// Handle --debug=value format
			if strings.HasPrefix(arg, "--debug=") {
				parts := strings.SplitN(arg, "=", 2)
				flags.DebugFile = parts[1]
				continue
			}

			// Handle standalone --debug
			if arg == "--debug" {
				flags.DebugFile = "stdout"
				continue
			}

			// Check if this flag takes a value
			if strings.HasPrefix(arg, "--org=") || strings.HasPrefix(arg, "--sprite=") {
				// Handle --flag=value format
				parts := strings.SplitN(arg, "=", 2)
				flagName := parts[0]
				flagValue := parts[1]

				switch flagName {
				case "--org":
					flags.Org = flagValue
				case "--sprite":
					flags.Sprite = flagValue
				}
				continue
			}

			// Handle short flags that might take values
			if strings.HasPrefix(arg, "-o") || strings.HasPrefix(arg, "-s") {
				if len(arg) == 2 {
					// Short flag without value, check next arg
					if i+1 < len(args) && !strings.HasPrefix(args[i+1], "-") {
						// Next arg is the value
						switch arg {
						case "-o":
							flags.Org = args[i+1]
						case "-s":
							flags.Sprite = args[i+1]
						}
						i++ // Skip the value in next iteration
						continue
					}
				} else if len(arg) > 2 {
					// Short flag with value attached (e.g., -omyorg)
					switch arg[0:2] {
					case "-o":
						flags.Org = arg[2:]
					case "-s":
						flags.Sprite = arg[2:]
					}
					continue
				}
			}

			// Handle help flags - only treat as global if they come before any command
			if (arg == "--help" || arg == "-h") && len(cleanedArgs) == 0 {
				flags.Help = true
				continue
			}
		}

		// Not a global flag, keep it
		cleanedArgs = append(cleanedArgs, arg)
	}

	return cleanedArgs, flags, nil
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
