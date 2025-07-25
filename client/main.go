package main

import (
	"flag"
	"fmt"
	"io"
	"log/slog"
	"os"

	"github.com/sprite-env/client/commands"
	"github.com/sprite-env/client/config"
)

var (
	clientLogger *slog.Logger
)

func setupLogger(debugFile string) {
	if debugFile != "" {
		var writer io.Writer

		// Special case: if debugFile is "-" or "stdout", log to stdout
		if debugFile == "-" || debugFile == "stdout" {
			writer = os.Stdout
		} else {
			// Create or open the debug log file
			file, err := os.OpenFile(debugFile, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0644)
			if err != nil {
				fmt.Fprintf(os.Stderr, "Error: Failed to open debug log file: %v\n", err)
				os.Exit(1)
			}
			writer = file
		}

		// Create a text handler with debug level
		opts := &slog.HandlerOptions{
			Level: slog.LevelDebug,
		}
		handler := slog.NewTextHandler(writer, opts)
		clientLogger = slog.New(handler)
		slog.SetDefault(clientLogger)
	} else {
		// Disable all logging by default - send to discard
		clientLogger = slog.New(slog.NewTextHandler(io.Discard, &slog.HandlerOptions{Level: slog.LevelError + 1}))
		slog.SetDefault(clientLogger)
	}
}

// debugLog logs at Debug level; output depends on logger configuration.
func debugLog(format string, a ...interface{}) {
	slog.Debug(fmt.Sprintf(format, a...))
}

func main() {
	// Define global flags using flag.CommandLine
	var globalDebug string
	var globalHelp bool

	flag.CommandLine.Init("sprite", flag.ContinueOnError)
	flag.StringVar(&globalDebug, "debug", "", "Enable debug logging (use 'stdout' or '-' for console, or specify a file path)")
	flag.BoolVar(&globalHelp, "help", false, "Show help")
	flag.BoolVar(&globalHelp, "h", false, "Show help")

	// Custom usage for global help
	flag.CommandLine.Usage = func() {
		printUsage()
	}

	// Parse global flags, but we need to handle --debug specially
	// Create a copy of os.Args to manipulate for --debug handling
	modifiedArgs := make([]string, len(os.Args))
	copy(modifiedArgs, os.Args)

	// Check for standalone --debug flag and convert it to --debug=stdout
	for i := 1; i < len(modifiedArgs); i++ {
		if modifiedArgs[i] == "--debug" {
			// Replace standalone --debug with --debug=stdout
			modifiedArgs[i] = "--debug=stdout"
		}
	}

	// Parse flags normally - flag package will handle --debug=value
	err := flag.CommandLine.Parse(modifiedArgs[1:])
	if err == flag.ErrHelp {
		// Help was explicitly requested
		printUsage()
		os.Exit(0)
	} else if err != nil {
		// Some other parsing error
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}

	// Setup logging based on debug flag
	setupLogger(globalDebug)

	// Get remaining args after global flags
	args := flag.Args()

	// Check if we need help or have no command
	if globalHelp || len(args) == 0 {
		printUsage()
		os.Exit(0)
	}

	// Initialize config manager
	cfg, err := config.NewManager()
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to initialize config: %v\n", err)
		os.Exit(1)
	}

	// Create global context to pass to commands
	globalCtx := &commands.GlobalContext{
		Debug:     globalDebug,
		ConfigMgr: cfg,
		Logger:    clientLogger,
	}

	// Get subcommand
	subcommand := args[0]
	subArgs := args[1:]

	switch subcommand {
	case "exec":
		commands.ExecCommand(globalCtx, subArgs)
	case "console":
		commands.ConsoleCommand(globalCtx, subArgs)
	case "checkpoint", "checkpoints", "c":
		commands.CheckpointCommand(globalCtx, subArgs)
	case "restore":
		commands.RestoreCommand(globalCtx, subArgs)
	case "create":
		commands.CreateCommand(globalCtx, subArgs)
	case "destroy":
		commands.DestroyCommand(globalCtx, subArgs)
	case "use":
		commands.UseCommand(globalCtx, subArgs)
	case "list":
		commands.ListCommand(globalCtx, subArgs)
	case "org", "orgs", "organizations":
		commands.OrgCommand(globalCtx, subArgs)
	case "transcripts":
		commands.TranscriptsCommand(globalCtx, subArgs)
	case "proxy":
		commands.ProxyCommand(globalCtx, subArgs)
	case "sync":
		commands.SyncCommand(cfg, subArgs)
	case "admin":
		commands.AdminCommand(globalCtx, subArgs)
	case "api":
		commands.ApiCommand(globalCtx, subArgs)
	default:
		slog.Error("Unknown command", "command", subcommand)
		printUsage()
		os.Exit(1)
	}
}

func printUsage() {
	fmt.Fprintf(os.Stderr, `sprite - Sprite Environment CLI

Usage:
  sprite [global options] <command> [command options] [arguments]

Commands:
  exec                      Execute a command in the sprite environment
  console                   Open an interactive shell in the sprite environment
  create <name>             Create a new sprite
  use [sprite]              Activate a sprite for the current directory
  list                      List all sprites
  checkpoint [subcommand]   Manage checkpoints (aliases: checkpoints, c)
    create                  Create a new checkpoint
    list                    List all checkpoints
    info <id>               Show information about a specific checkpoint
  restore <id>              Restore from a checkpoint
  destroy                   Destroy the current sprite
  transcripts <subcommand>  Manage transcript recording
    enable                  Enable transcript recording for future exec calls
    disable                 Disable transcript recording for future exec calls
  proxy <port1> [port2...]  Forward local ports through the remote server proxy
  sync                      Synchronize git repository to sprite environment
  api [options] <path>      Make authenticated API calls with curl

Organization Commands:
  org auth                  Add an API token (aliases: orgs, organizations)
  org list                  Show configured tokens
  org logout                Remove all tokens

Global Options:
  --debug[=<file>]          Enable debug logging (logs to stdout if no file specified)
  -h, --help                Show this help message

Command Options:
  -o, --org <name>          Specify organization (for sprite commands)
  -s, --sprite <name>       Specify sprite (for sprite commands)
  -h, --help                Show help for specific command

Examples:
  # Authenticate with an organization
  sprite org auth
  sprite orgs auth

  # Create a new sprite
  sprite create my-sprite
  sprite create -o myorg dev-sprite

  # List all sprites
  sprite list
  sprite list -o myorg

  # Activate a sprite for the current directory
  sprite use my-sprite
  sprite use -o myorg dev-sprite
  sprite use --unset

  # Execute a command
  sprite exec ls -la
  sprite exec -o myorg -s mysprite npm start

  # Open an interactive shell
  sprite console
  sprite console -o myorg -s mysprite

  # Execute with debug logging
  sprite --debug exec npm start              # logs to stdout
  sprite --debug=/tmp/debug.log exec npm start  # logs to file

  # Create a checkpoint
  sprite checkpoint create

  # List checkpoints
  sprite checkpoint list

  # Restore from checkpoint
  sprite restore my-checkpoint-id

  # Destroy current sprite
  sprite destroy

  # Enable transcript recording
  sprite transcripts enable

  # Disable transcript recording
  sprite transcripts disable

  # Forward local ports 8080 and 3000
  sprite proxy 8080 3000

Use 'sprite <command> --help' for command-specific options.
`)
}
