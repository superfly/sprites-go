package main

import (
	"fmt"
	"os"
	"strings"

	"github.com/sprite-env/client/commands"
	"github.com/sprite-env/client/config"
	"github.com/urfave/cli/v2"
)

// SpriteRunner wraps the sprite client execution functionality
type SpriteRunner struct {
	cfg *config.Manager
}

// NewSpriteRunner creates a new sprite runner instance
func NewSpriteRunner() (*SpriteRunner, error) {
	cfg, err := config.NewManager()
	if err != nil {
		return nil, fmt.Errorf("failed to initialize config: %w", err)
	}
	return &SpriteRunner{cfg: cfg}, nil
}

// RunCommand executes a command in a sprite environment
func (sr *SpriteRunner) RunCommand(cmd string, args []string, org, sprite, workingDir string, env []string, tty bool) int {
	// Build the command arguments for the sprite client
	execArgs := []string{}

	// Add organization and sprite flags if specified
	if org != "" {
		execArgs = append(execArgs, "-o", org)
	}
	if sprite != "" {
		execArgs = append(execArgs, "-s", sprite)
	}

	// Add working directory if specified
	if workingDir != "" {
		execArgs = append(execArgs, "-dir", workingDir)
	}

	// Add environment variables if specified
	if len(env) > 0 {
		execArgs = append(execArgs, "-env", strings.Join(env, ","))
	}

	// Add TTY flag if needed
	if tty {
		execArgs = append(execArgs, "-tty")
	}

	// Add the command and its arguments
	execArgs = append(execArgs, cmd)
	execArgs = append(execArgs, args...)

	// Execute using the existing sprite client
	commands.ExecCommand(sr.cfg, execArgs)

	// The ExecCommand function handles its own exit, so we shouldn't reach here
	// But in case we do, return a generic error code
	return 1
}

func main() {
	// Create sprite runner
	runner, err := NewSpriteRunner()
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}

	app := &cli.App{
		Name:  "sprite-run",
		Usage: "Run programs inside sprite environments",
		Description: "sprite-run wraps program execution to run inside sprite environments. " +
			"Programs appear to run locally, similar to running under tmux.",
		Version: "1.0.0",
		Flags: []cli.Flag{
			&cli.StringFlag{
				Name:    "org",
				Aliases: []string{"o"},
				Usage:   "Specify organization",
				EnvVars: []string{"SPRITE_ORG"},
			},
			&cli.StringFlag{
				Name:    "sprite",
				Aliases: []string{"s"},
				Usage:   "Specify sprite name",
				EnvVars: []string{"SPRITE_NAME"},
			},
			&cli.StringFlag{
				Name:    "dir",
				Aliases: []string{"d"},
				Usage:   "Working directory for the command",
			},
			&cli.StringSliceFlag{
				Name:    "env",
				Aliases: []string{"e"},
				Usage:   "Environment variables (KEY=value)",
			},
			&cli.BoolFlag{
				Name:    "tty",
				Aliases: []string{"t"},
				Usage:   "Allocate a pseudo-TTY (default: true for interactive programs)",
				Value:   false, // We'll auto-detect for known programs
			},
		},
		Commands: []*cli.Command{
			{
				Name:  "nano",
				Usage: "Run nano text editor",
				Description: "Run the nano text editor inside a sprite environment. " +
					"All nano command line options are supported.",
				ArgsUsage: "[file...]",
				Action: func(ctx *cli.Context) error {
					// nano always needs TTY
					tty := true
					if ctx.IsSet("tty") {
						tty = ctx.Bool("tty")
					}

					exitCode := runner.RunCommand(
						"nano",
						ctx.Args().Slice(),
						ctx.String("org"),
						ctx.String("sprite"),
						ctx.String("dir"),
						ctx.StringSlice("env"),
						tty,
					)
					os.Exit(exitCode)
					return nil
				},
			},
		},
		Before: func(ctx *cli.Context) error {
			// Validate that we have the necessary sprite configuration
			if ctx.String("org") == "" && ctx.String("sprite") == "" {
				// Check if we have environment variables set
				if os.Getenv("SPRITE_URL") == "" && os.Getenv("SPRITE_ORG") == "" {
					fmt.Fprintf(os.Stderr, "Error: No sprite configuration found.\n")
					fmt.Fprintf(os.Stderr, "Please specify --org and --sprite, or set SPRITE_ORG and SPRITE_NAME environment variables.\n")
					fmt.Fprintf(os.Stderr, "You can also set SPRITE_URL and SPRITE_TOKEN for direct connections.\n")
					return cli.Exit("", 1)
				}
			}
			return nil
		},
		ExitErrHandler: func(ctx *cli.Context, err error) {
			// Handle exit errors gracefully
			if err != nil {
				fmt.Fprintf(os.Stderr, "Error: %v\n", err)
				os.Exit(1)
			}
		},
	}

	// Run the CLI application
	if err := app.Run(os.Args); err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}
}
