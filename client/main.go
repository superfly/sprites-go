package main

import (
	"bufio"
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"lib/api"
	"net/http"
	"os"
	"strings"
	"time"
)

func main() {
	if len(os.Args) < 2 {
		printUsage()
		os.Exit(1)
	}

	// Get environment variables
	url := os.Getenv("SPRITE_URL")
	token := os.Getenv("SPRITE_TOKEN")

	if url == "" {
		fmt.Fprintf(os.Stderr, "Error: SPRITE_URL environment variable not set\n")
		os.Exit(1)
	}

	if token == "" {
		fmt.Fprintf(os.Stderr, "Error: SPRITE_TOKEN environment variable not set\n")
		os.Exit(1)
	}

	// Ensure URL doesn't have trailing slash
	url = strings.TrimRight(url, "/")

	subcommand := os.Args[1]

	switch subcommand {
	case "exec":
		// Dispatch to exec command
		execCommand(url, token, os.Args[2:])
	case "checkpoint", "checkpoints", "c":
		// Handle checkpoint command (accepts checkpoint, checkpoints, or c)
		checkpointCommand(url, token, os.Args[2:])
	case "restore":
		// Handle restore command
		restoreCommand(url, token, os.Args[2:])
	case "help", "-h", "--help":
		printUsage()
		os.Exit(0)
	default:
		fmt.Fprintf(os.Stderr, "Error: Unknown command '%s'\n\n", subcommand)
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
    create <id>             Create a new checkpoint
    list                    List all checkpoints
  restore <id>              Restore from a checkpoint

Environment Variables:
  SPRITE_URL    Base URL of the Sprite API (required)
  SPRITE_TOKEN  Authentication token (required)

Examples:
  # Execute a command
  sprite-client exec ls -la

  # Create a checkpoint
  sprite-client checkpoint create my-checkpoint-id

  # List checkpoints
  sprite-client checkpoint list

  # Restore from checkpoint
  sprite-client restore my-checkpoint-id

Use 'sprite-client exec -h' for exec command options.
`)
}

func checkpointCommand(baseURL, token string, args []string) {
	if len(args) < 1 {
		fmt.Fprintf(os.Stderr, "Error: checkpoint requires a subcommand\n")
		fmt.Fprintf(os.Stderr, "Usage: sprite-client checkpoint <create|list> [arguments]\n")
		os.Exit(1)
	}

	subcommand := args[0]
	subArgs := args[1:]

	switch subcommand {
	case "create":
		checkpointCreateCommand(baseURL, token, subArgs)
	case "list":
		checkpointListCommand(baseURL, token, subArgs)
	default:
		fmt.Fprintf(os.Stderr, "Error: Unknown checkpoint subcommand '%s'\n", subcommand)
		fmt.Fprintf(os.Stderr, "Usage: sprite-client checkpoint <create|list> [arguments]\n")
		os.Exit(1)
	}
}

func checkpointCreateCommand(baseURL, token string, args []string) {
	if len(args) != 1 {
		fmt.Fprintf(os.Stderr, "Error: checkpoint create requires exactly one argument (checkpoint ID)\n")
		fmt.Fprintf(os.Stderr, "Usage: sprite-client checkpoint create <checkpoint-id>\n")
		os.Exit(1)
	}

	checkpointID := args[0]

	// Create request
	req := api.CheckpointRequest{
		CheckpointID: checkpointID,
	}

	jsonData, err := json.Marshal(req)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create request: %v\n", err)
		os.Exit(1)
	}

	// Make HTTP request
	url := fmt.Sprintf("%s/checkpoint", baseURL)
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
	if len(args) != 0 {
		fmt.Fprintf(os.Stderr, "Error: checkpoint list takes no arguments\n")
		fmt.Fprintf(os.Stderr, "Usage: sprite-client checkpoint list\n")
		os.Exit(1)
	}

	// Make HTTP request
	url := fmt.Sprintf("%s/checkpoints", baseURL)
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

	// Parse response
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

	fmt.Printf("%-30s %-25s %s\n", "ID", "CREATED", "SOURCE")
	fmt.Printf("%-30s %-25s %s\n", strings.Repeat("-", 30), strings.Repeat("-", 25), strings.Repeat("-", 20))

	for _, cp := range checkpoints {
		created := cp.CreateTime.Format(time.RFC3339)
		source := cp.SourceID
		if source == "" {
			source = "-"
		}
		fmt.Printf("%-30s %-25s %s\n", cp.ID, created, source)
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
