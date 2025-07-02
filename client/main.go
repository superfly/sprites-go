package main

import (
	"bufio"
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"os"
	"strings"
	"time"

	"github.com/sprite-env/lib/api"
)

var clientLogger *slog.Logger

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
	if len(os.Args) < 2 {
		printUsage()
		os.Exit(1)
	}

	// Get environment variables
	url := os.Getenv("SPRITE_URL")
	token := os.Getenv("SPRITE_TOKEN")

	if url == "" {
		slog.Error("SPRITE_URL environment variable not set")
		os.Exit(1)
	}

	if token == "" {
		slog.Error("SPRITE_TOKEN environment variable not set")
		os.Exit(1)
	}

	// Ensure URL doesn't have trailing slash
	url = strings.TrimRight(url, "/")

	// Scan all args for --debug flag and remove it
	debug := false
	filtered := make([]string, 0, len(os.Args))
	for _, arg := range os.Args {
		if arg == "--debug" {
			debug = true
		} else {
			filtered = append(filtered, arg)
		}
	}
	os.Args = filtered
	setupLogger(debug)

	subcommand := os.Args[1]

	switch subcommand {
	case "exec":
		// Dispatch to exec command
		execCommand(url, token, os.Args[2:])
	case "admin":
		// Handle admin commands
		adminCommand(url, token, os.Args[2:])
	case "checkpoint", "checkpoints", "c":
		// Handle checkpoint command (accepts checkpoint, checkpoints, or c)
		checkpointCommand(url, token, os.Args[2:])
	case "restore":
		// Handle restore command
		restoreCommand(url, token, os.Args[2:])
	case "transcripts":
		// Handle transcripts command
		transcriptsCommand(url, token, os.Args[2:])
	case "proxy":
		// Handle proxy command
		proxyCommand(url, token, os.Args[2:])
	case "help", "-h", "--help":
		printUsage()
		os.Exit(0)
	default:
		slog.Error("Unknown command", "command", subcommand)
		printUsage()
		os.Exit(1)
	}
}

func printUsage() {
	fmt.Fprintf(os.Stderr, `sprite-client - Sprite Environment API Client

Usage:
  sprite-client <command> [arguments]

Commands:
  exec                      Execute a command in the sprite environment
  checkpoint <subcommand>   Manage checkpoints (aliases: checkpoints, c)
    create                  Create a new checkpoint
    list                    List all checkpoints
    info <id>               Show information about a specific checkpoint
  restore <id>              Restore from a checkpoint
  transcripts <subcommand>  Manage transcript recording
    enable                  Enable transcript recording for future exec calls
    disable                 Disable transcript recording for future exec calls
  proxy <port1> [port2...]  Forward local ports through the remote server proxy

Environment Variables:
  SPRITE_URL    Base URL of the Sprite API (required)
  SPRITE_TOKEN  Authentication token (required)
  SPRITE_ADMIN_TOKEN  Admin authentication token (optional, for admin commands)

Examples:
  # Execute a command
  sprite-client exec ls -la

  # Create a checkpoint
  sprite-client checkpoint create

  # List checkpoints
  sprite-client checkpoint list

  # Get checkpoint info
  sprite-client checkpoint info v3

  # Restore from checkpoint
  sprite-client restore my-checkpoint-id

  # Enable transcript recording
  sprite-client transcripts enable

  # Disable transcript recording
  sprite-client transcripts disable

  # Forward local ports 8080 and 3000
  sprite-client proxy 8080 3000

Use 'sprite-client exec -h' for exec command options.
`)
}

func adminCommand(baseURL, token string, args []string) {
	if len(args) < 1 {
		fmt.Fprintf(os.Stderr, "Error: admin requires a subcommand\n")
		fmt.Fprintf(os.Stderr, "Usage: sprite-client admin <reset-state> [arguments]\n")
		os.Exit(1)
	}

	subcommand := args[0]
	subArgs := args[1:]

	switch subcommand {
	case "reset-state":
		adminResetStateCommand(baseURL, token, subArgs)
	default:
		fmt.Fprintf(os.Stderr, "Error: Unknown admin subcommand '%s'\n", subcommand)
		fmt.Fprintf(os.Stderr, "Usage: sprite-client admin <reset-state> [arguments]\n")
		os.Exit(1)
	}
}

func adminResetStateCommand(baseURL, token string, args []string) {
	if len(args) != 0 {
		fmt.Fprintf(os.Stderr, "Error: admin reset-state takes no arguments\n")
		fmt.Fprintf(os.Stderr, "Usage: sprite-client admin reset-state\n")
		os.Exit(1)
	}

	// Check if admin token is set in environment
	adminToken := os.Getenv("SPRITE_ADMIN_TOKEN")
	if adminToken != "" {
		token = adminToken
	}

	// Make HTTP request
	url := fmt.Sprintf("%s/admin/reset-state", baseURL)
	debugLog("HTTP request: %s %s", "POST", url)

	httpReq, err := http.NewRequest("POST", url, nil)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create HTTP request: %v\n", err)
		os.Exit(1)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", token))

	client := &http.Client{}
	debugLog("Sending HTTP request")
	resp, err := client.Do(httpReq)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to make request: %v\n", err)
		os.Exit(1)
	}
	defer resp.Body.Close()

	body, _ := io.ReadAll(resp.Body)

	if resp.StatusCode == http.StatusForbidden {
		fmt.Fprintf(os.Stderr, "Error: Admin authentication required. Set SPRITE_ADMIN_TOKEN environment variable.\n")
		os.Exit(1)
	}

	if resp.StatusCode != http.StatusOK {
		fmt.Fprintf(os.Stderr, "Error: API returned status %d: %s\n", resp.StatusCode, string(body))
		os.Exit(1)
	}

	fmt.Print(string(body))
}

func checkpointCommand(baseURL, token string, args []string) {
	if len(args) < 1 {
		fmt.Fprintf(os.Stderr, "Error: checkpoint requires a subcommand\n")
		fmt.Fprintf(os.Stderr, "Usage: sprite-client checkpoint <create|list|info> [arguments]\n")
		os.Exit(1)
	}

	subcommand := args[0]
	subArgs := args[1:]

	switch subcommand {
	case "create":
		checkpointCreateCommand(baseURL, token, subArgs)
	case "list":
		checkpointListCommand(baseURL, token, subArgs)
	case "info":
		checkpointInfoCommand(baseURL, token, subArgs)
	default:
		fmt.Fprintf(os.Stderr, "Error: Unknown checkpoint subcommand '%s'\n", subcommand)
		fmt.Fprintf(os.Stderr, "Usage: sprite-client checkpoint <create|list|info> [arguments]\n")
		os.Exit(1)
	}
}

func checkpointCreateCommand(baseURL, token string, args []string) {
	if len(args) != 0 {
		fmt.Fprintf(os.Stderr, "Error: checkpoint create takes no arguments\n")
		fmt.Fprintf(os.Stderr, "Usage: sprite-client checkpoint create\n")
		os.Exit(1)
	}

	// Create empty request (backward compatible)
	req := api.CheckpointRequest{}

	jsonData, err := json.Marshal(req)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create request: %v\n", err)
		os.Exit(1)
	}

	// Make HTTP request
	url := fmt.Sprintf("%s/checkpoint", baseURL)
	debugLog("HTTP request: %s %s", "POST", url)

	httpReq, err := http.NewRequest("POST", url, bytes.NewReader(jsonData))
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create HTTP request: %v\n", err)
		os.Exit(1)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", token))
	httpReq.Header.Set("Content-Type", "application/json")

	// Use client with no timeout for streaming
	client := &http.Client{
		Timeout: 0,
	}
	resp, err := client.Do(httpReq)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to make request: %v\n", err)
		os.Exit(1)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		fmt.Fprintf(os.Stderr, "Error: API returned status %d: %s\n", resp.StatusCode, string(body))
		os.Exit(1)
	}

	// Process streaming response
	exitCode := processStreamingResponse(resp.Body)
	os.Exit(exitCode)
}

func checkpointListCommand(baseURL, token string, args []string) {
	var historyFilter string

	// Simple flag parsing for --history
	if len(args) > 0 {
		for i := 0; i < len(args); i++ {
			if args[i] == "--history" && i+1 < len(args) {
				historyFilter = args[i+1]
				break
			}
		}

		if historyFilter == "" {
			fmt.Fprintf(os.Stderr, "Error: invalid arguments\n")
			fmt.Fprintf(os.Stderr, "Usage: sprite-client checkpoint list [--history VERSION]\n")
			os.Exit(1)
		}
	}

	// Make HTTP request
	url := fmt.Sprintf("%s/checkpoints", baseURL)
	debugLog("HTTP request: %s %s", "GET", url)
	if historyFilter != "" {
		url += fmt.Sprintf("?history=%s", historyFilter)
	}

	httpReq, err := http.NewRequest("GET", url, nil)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create HTTP request: %v\n", err)
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

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		fmt.Fprintf(os.Stderr, "Error: API returned status %d: %s\n", resp.StatusCode, string(body))
		os.Exit(1)
	}

	// Check content type
	contentType := resp.Header.Get("Content-Type")
	if strings.HasPrefix(contentType, "text/plain") {
		// History filter results - just print as-is
		body, _ := io.ReadAll(resp.Body)
		fmt.Print(string(body))
		return
	}

	// Parse JSON response
	var checkpoints []api.CheckpointInfo
	if err := json.NewDecoder(resp.Body).Decode(&checkpoints); err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to parse response: %v\n", err)
		os.Exit(1)
	}

	// Display checkpoints
	if len(checkpoints) == 0 {
		fmt.Println("No checkpoints found.")
		return
	}

	fmt.Printf("%-30s %s\n", "ID", "CREATED")
	fmt.Printf("%-30s %s\n", strings.Repeat("-", 30), strings.Repeat("-", 25))

	for _, cp := range checkpoints {
		created := cp.CreateTime.Format(time.RFC3339)
		fmt.Printf("%-30s %s\n", cp.ID, created)
	}
}

func checkpointInfoCommand(baseURL, token string, args []string) {
	if len(args) != 1 {
		fmt.Fprintf(os.Stderr, "Error: checkpoint info requires exactly one argument (checkpoint ID)\n")
		fmt.Fprintf(os.Stderr, "Usage: sprite-client checkpoint info <checkpoint-id>\n")
		os.Exit(1)
	}

	checkpointID := args[0]

	// Make HTTP request
	url := fmt.Sprintf("%s/checkpoints/%s", baseURL, checkpointID)
	debugLog("HTTP request: %s %s", "GET", url)

	httpReq, err := http.NewRequest("GET", url, nil)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create HTTP request: %v\n", err)
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

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		fmt.Fprintf(os.Stderr, "Error: API returned status %d: %s\n", resp.StatusCode, string(body))
		os.Exit(1)
	}

	// Check content type
	contentType := resp.Header.Get("Content-Type")
	if strings.HasPrefix(contentType, "text/plain") {
		// History filter results - just print as-is
		body, _ := io.ReadAll(resp.Body)
		fmt.Print(string(body))
		return
	}

	// Parse JSON response
	var checkpoint api.CheckpointInfo
	if err := json.NewDecoder(resp.Body).Decode(&checkpoint); err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to parse response: %v\n", err)
		os.Exit(1)
	}

	// Display checkpoint information
	fmt.Printf("ID: %s\n", checkpoint.ID)
	fmt.Printf("Created: %s\n", checkpoint.CreateTime.Format(time.RFC3339))

	if len(checkpoint.History) > 0 {
		fmt.Println("History:")
		for _, entry := range checkpoint.History {
			fmt.Printf("  %s\n", entry)
		}
	} else {
		fmt.Println("History: (none)")
	}
}

func restoreCommand(baseURL, token string, args []string) {
	if len(args) != 1 {
		fmt.Fprintf(os.Stderr, "Error: restore requires exactly one argument (checkpoint ID)\n")
		fmt.Fprintf(os.Stderr, "Usage: sprite-client restore <checkpoint-id>\n")
		os.Exit(1)
	}

	checkpointID := args[0]

	// Make HTTP request to new endpoint
	url := fmt.Sprintf("%s/checkpoints/%s/restore", baseURL, checkpointID)
	debugLog("HTTP request: %s %s", "POST", url)

	httpReq, err := http.NewRequest("POST", url, nil)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create HTTP request: %v\n", err)
		os.Exit(1)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", token))

	// Use client with no timeout for streaming
	client := &http.Client{
		Timeout: 0,
	}
	resp, err := client.Do(httpReq)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to make request: %v\n", err)
		os.Exit(1)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		fmt.Fprintf(os.Stderr, "Error: API returned status %d: %s\n", resp.StatusCode, string(body))
		os.Exit(1)
	}

	// Process streaming response
	exitCode := processStreamingResponse(resp.Body)
	os.Exit(exitCode)
}

func transcriptsCommand(baseURL, token string, args []string) {
	if len(args) < 1 {
		fmt.Fprintf(os.Stderr, "Error: transcripts requires a subcommand\n")
		fmt.Fprintf(os.Stderr, "Usage: sprite-client transcripts <enable|disable>\n")
		os.Exit(1)
	}

	subcommand := args[0]
	subArgs := args[1:]

	switch subcommand {
	case "enable":
		transcriptsEnableCommand(baseURL, token, subArgs)
	case "disable":
		transcriptsDisableCommand(baseURL, token, subArgs)
	default:
		fmt.Fprintf(os.Stderr, "Error: Unknown transcripts subcommand '%s'\n", subcommand)
		fmt.Fprintf(os.Stderr, "Usage: sprite-client transcripts <enable|disable>\n")
		os.Exit(1)
	}
}

func transcriptsEnableCommand(baseURL, token string, args []string) {
	if len(args) != 0 {
		fmt.Fprintf(os.Stderr, "Error: transcripts enable takes no arguments\n")
		fmt.Fprintf(os.Stderr, "Usage: sprite-client transcripts enable\n")
		os.Exit(1)
	}

	// Make HTTP request
	url := fmt.Sprintf("%s/transcripts/enable", baseURL)
	debugLog("HTTP request: %s %s", "POST", url)

	httpReq, err := http.NewRequest("POST", url, nil)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create HTTP request: %v\n", err)
		os.Exit(1)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", token))

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

func transcriptsDisableCommand(baseURL, token string, args []string) {
	if len(args) != 0 {
		fmt.Fprintf(os.Stderr, "Error: transcripts disable takes no arguments\n")
		fmt.Fprintf(os.Stderr, "Usage: sprite-client transcripts disable\n")
		os.Exit(1)
	}

	// Make HTTP request
	url := fmt.Sprintf("%s/transcripts/disable", baseURL)
	debugLog("HTTP request: %s %s", "POST", url)

	httpReq, err := http.NewRequest("POST", url, nil)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create HTTP request: %v\n", err)
		os.Exit(1)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", token))

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

// processStreamingResponse processes NDJSON streaming responses
func processStreamingResponse(reader io.Reader) int {
	scanner := bufio.NewScanner(reader)
	exitCode := 0
	hasError := false

	for scanner.Scan() {
		line := scanner.Text()
		if line == "" {
			continue
		}

		var msg api.StreamMessage
		if err := json.Unmarshal([]byte(line), &msg); err != nil {
			fmt.Fprintf(os.Stderr, "Error: Failed to parse message: %v\n", err)
			continue
		}

		switch msg.Type {
		case "info":
			fmt.Println(msg.Data)
		case "stdout":
			fmt.Println(msg.Data)
		case "stderr":
			fmt.Fprintln(os.Stderr, msg.Data)
		case "error":
			fmt.Fprintf(os.Stderr, "Error: %s\n", msg.Error)
			hasError = true
			if exitCode == 0 {
				exitCode = 1
			}
		case "complete":
			fmt.Println(msg.Data)
		}
	}

	if err := scanner.Err(); err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to read stream: %v\n", err)
		if exitCode == 0 {
			exitCode = 1
		}
	}

	if hasError && exitCode == 0 {
		exitCode = 1
	}

	return exitCode
}
