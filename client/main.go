package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"os"

	"github.com/sprite-env/client/commands"
	"github.com/sprite-env/client/config"
	"github.com/sprite-env/lib/api"
)

var (
	clientLogger *slog.Logger
	globalDebug  bool
	globalHelp   bool
)

func setupLogger(debug bool) {
	level := slog.LevelInfo
	if debug {
		level = slog.LevelDebug
	}
	clientLogger = slog.New(slog.NewTextHandler(os.Stderr, &slog.HandlerOptions{Level: level}))
	slog.SetDefault(clientLogger)
}

// debugLog logs at Debug level; output depends on logger configuration.
func debugLog(format string, a ...interface{}) {
	slog.Debug(fmt.Sprintf(format, a...))
}

func main() {
	// Parse global flags first
	globalFlags := flag.NewFlagSet("sprite", flag.ContinueOnError)
	globalFlags.BoolVar(&globalDebug, "debug", false, "Enable debug logging")
	globalFlags.BoolVar(&globalHelp, "help", false, "Show help")
	globalFlags.BoolVar(&globalHelp, "h", false, "Show help")

	// Custom usage for global help
	globalFlags.Usage = func() {
		printUsage()
	}

	// Parse only known flags, ignore unknown ones for subcommands
	globalFlags.Parse(os.Args[1:])

	// Setup logging based on debug flag
	setupLogger(globalDebug)

	// Get remaining args after global flags
	args := globalFlags.Args()

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

	// Get subcommand
	subcommand := args[0]
	subArgs := args[1:]

	switch subcommand {
	case "exec":
		commands.ExecCommand(cfg, subArgs)
	case "checkpoint", "checkpoints", "c":
		commands.CheckpointCommand(cfg, subArgs)
	case "restore":
		commands.RestoreCommand(cfg, subArgs)
	case "destroy":
		commands.DestroyCommand(cfg, subArgs)
	case "org":
		commands.OrgCommand(cfg, subArgs)
	case "transcripts":
		// Handle transcripts command using config
		handleTranscriptsCommand(cfg, subArgs)
	case "proxy":
		// TODO: Move proxy command to commands package
		proxyCommandPlaceholder(cfg, subArgs)
	case "admin":
		// TODO: Move admin command to commands package if needed
		adminCommand(cfg, subArgs)
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

Organization Commands:
  org auth                  Add an API token
  org list                  Show configured tokens
  org logout                Remove all tokens

Global Options:
  --debug                   Enable debug logging
  -h, --help                Show this help message

Command Options:
  -o, --org <name>          Specify organization (for sprite commands)
  -s, --sprite <name>       Specify sprite (for sprite commands)
  -h, --help                Show help for specific command

Examples:
  # Authenticate with an organization
  sprite org auth

  # Execute a command
  sprite exec ls -la
  sprite exec -o myorg -s mysprite npm start

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

// handleTranscriptsCommand handles the transcripts command using the config system
func handleTranscriptsCommand(cfg *config.Manager, args []string) {
	if len(args) < 1 {
		fmt.Fprintf(os.Stderr, "Error: transcripts requires a subcommand\n")
		fmt.Fprintf(os.Stderr, "Usage: sprite transcripts <enable|disable>\n")
		os.Exit(1)
	}

	subcommand := args[0]
	subArgs := args[1:]

	switch subcommand {
	case "enable":
		transcriptsEnableCommand(cfg, subArgs)
	case "disable":
		transcriptsDisableCommand(cfg, subArgs)
	default:
		fmt.Fprintf(os.Stderr, "Error: Unknown transcripts subcommand '%s'\n", subcommand)
		fmt.Fprintf(os.Stderr, "Usage: sprite transcripts <enable|disable>\n")
		os.Exit(1)
	}
}

func transcriptsEnableCommand(cfg *config.Manager, args []string) {
	if len(args) != 0 {
		fmt.Fprintf(os.Stderr, "Error: transcripts enable takes no arguments\n")
		fmt.Fprintf(os.Stderr, "Usage: sprite transcripts enable\n")
		os.Exit(1)
	}

	// Get current organization
	org := cfg.GetCurrentOrg()
	if org == nil {
		fmt.Fprintf(os.Stderr, "Error: No organization configured. Please run 'sprite org auth' first\n")
		os.Exit(1)
	}

	// Make HTTP request
	url := fmt.Sprintf("%s/transcripts/enable", org.URL)
	debugLog("HTTP request: %s %s", "POST", url)

	httpReq, err := http.NewRequest("POST", url, nil)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create HTTP request: %v\n", err)
		os.Exit(1)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", org.Token))

	client := &http.Client{}
	resp, err := client.Do(httpReq)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to make HTTP request: %v\n", err)
		os.Exit(1)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		fmt.Fprintf(os.Stderr, "Error: HTTP %d: %s\n", resp.StatusCode, string(body))
		os.Exit(1)
	}

	// Parse JSON response
	var response api.TranscriptsResponse
	if err := json.NewDecoder(resp.Body).Decode(&response); err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to parse response: %v\n", err)
		os.Exit(1)
	}

	if response.Enabled {
		fmt.Println("Transcripts enabled successfully.")
	} else {
		fmt.Fprintf(os.Stderr, "Error: Expected transcripts to be enabled, but got disabled response\n")
		os.Exit(1)
	}
}

func transcriptsDisableCommand(cfg *config.Manager, args []string) {
	if len(args) != 0 {
		fmt.Fprintf(os.Stderr, "Error: transcripts disable takes no arguments\n")
		fmt.Fprintf(os.Stderr, "Usage: sprite transcripts disable\n")
		os.Exit(1)
	}

	// Get current organization
	org := cfg.GetCurrentOrg()
	if org == nil {
		fmt.Fprintf(os.Stderr, "Error: No organization configured. Please run 'sprite org auth' first\n")
		os.Exit(1)
	}

	// Make HTTP request
	url := fmt.Sprintf("%s/transcripts/disable", org.URL)
	debugLog("HTTP request: %s %s", "POST", url)

	httpReq, err := http.NewRequest("POST", url, nil)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create HTTP request: %v\n", err)
		os.Exit(1)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", org.Token))

	client := &http.Client{}
	resp, err := client.Do(httpReq)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to make HTTP request: %v\n", err)
		os.Exit(1)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		fmt.Fprintf(os.Stderr, "Error: HTTP %d: %s\n", resp.StatusCode, string(body))
		os.Exit(1)
	}

	// Parse JSON response
	var response api.TranscriptsResponse
	if err := json.NewDecoder(resp.Body).Decode(&response); err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to parse response: %v\n", err)
		os.Exit(1)
	}

	if !response.Enabled {
		fmt.Println("Transcripts disabled successfully.")
	} else {
		fmt.Fprintf(os.Stderr, "Error: Expected transcripts to be disabled, but got enabled response\n")
		os.Exit(1)
	}
}

// TODO: Move these placeholder functions to commands package
func proxyCommandPlaceholder(cfg *config.Manager, args []string) {
	// For now, we need to get org credentials and use the old proxy implementation
	org := cfg.GetCurrentOrg()
	if org == nil {
		// Try environment variables for backward compatibility
		url := os.Getenv("SPRITE_URL")
		token := os.Getenv("SPRITE_TOKEN")
		if url == "" || token == "" {
			fmt.Fprintf(os.Stderr, "Error: No organization configured. Please run 'sprite org auth' first\n")
			os.Exit(1)
		}
		proxyCommand(url, token, args)
	} else {
		proxyCommand(org.URL, org.Token, args)
	}
}

func adminCommand(cfg *config.Manager, args []string) {
	fmt.Fprintf(os.Stderr, "Error: admin command not yet implemented in new structure\n")
	os.Exit(1)
}
