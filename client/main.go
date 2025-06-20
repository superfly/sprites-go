package sprite

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"os"
	"strings"
)

// CheckpointRequest represents the checkpoint API request
type CheckpointRequest struct {
	CheckpointID string `json:"checkpoint_id"`
}

// RestoreRequest represents the restore API request
type RestoreRequest struct {
	CheckpointID string `json:"checkpoint_id"`
}

// APIResponse represents a generic API response
type APIResponse struct {
	Status       string `json:"status,omitempty"`
	CheckpointID string `json:"checkpoint_id,omitempty"`
	Error        string `json:"error,omitempty"`
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
	case "checkpoint":
		// Handle checkpoint command
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
  exec         Execute a command in the sprite environment
  checkpoint   Create a checkpoint
  restore      Restore from a checkpoint

Environment Variables:
  SPRITE_URL    Base URL of the Sprite API (required)
  SPRITE_TOKEN  Authentication token (required)

Examples:
  # Execute a command
  sprite-client exec ls -la

  # Create a checkpoint
  sprite-client checkpoint my-checkpoint-id

  # Restore from checkpoint
  sprite-client restore my-checkpoint-id

Use 'sprite-client exec -h' for exec command options.
`)
}

func checkpointCommand(baseURL, token string, args []string) {
	if len(args) != 1 {
		fmt.Fprintf(os.Stderr, "Error: checkpoint requires exactly one argument (checkpoint ID)\n")
		fmt.Fprintf(os.Stderr, "Usage: sprite-client checkpoint <checkpoint-id>\n")
		os.Exit(1)
	}

	checkpointID := args[0]

	// Create request
	req := CheckpointRequest{
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

	client := &http.Client{}
	resp, err := client.Do(httpReq)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to make request: %v\n", err)
		os.Exit(1)
	}
	defer resp.Body.Close()

	// Read response
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to read response: %v\n", err)
		os.Exit(1)
	}

	if resp.StatusCode != http.StatusAccepted && resp.StatusCode != http.StatusOK {
		fmt.Fprintf(os.Stderr, "Error: API returned status %d: %s\n", resp.StatusCode, string(body))
		os.Exit(1)
	}

	// Parse and display response
	var apiResp APIResponse
	if err := json.Unmarshal(body, &apiResp); err != nil {
		fmt.Printf("Checkpoint requested (ID: %s)\n", checkpointID)
	} else {
		fmt.Printf("Status: %s\n", apiResp.Status)
		fmt.Printf("Checkpoint ID: %s\n", apiResp.CheckpointID)
	}
}

func restoreCommand(baseURL, token string, args []string) {
	if len(args) != 1 {
		fmt.Fprintf(os.Stderr, "Error: restore requires exactly one argument (checkpoint ID)\n")
		fmt.Fprintf(os.Stderr, "Usage: sprite-client restore <checkpoint-id>\n")
		os.Exit(1)
	}

	checkpointID := args[0]

	// Create request
	req := RestoreRequest{
		CheckpointID: checkpointID,
	}

	jsonData, err := json.Marshal(req)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create request: %v\n", err)
		os.Exit(1)
	}

	// Make HTTP request
	url := fmt.Sprintf("%s/restore", baseURL)
	httpReq, err := http.NewRequest("POST", url, bytes.NewReader(jsonData))
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create HTTP request: %v\n", err)
		os.Exit(1)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", token))
	httpReq.Header.Set("Content-Type", "application/json")

	client := &http.Client{}
	resp, err := client.Do(httpReq)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to make request: %v\n", err)
		os.Exit(1)
	}
	defer resp.Body.Close()

	// Read response
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to read response: %v\n", err)
		os.Exit(1)
	}

	if resp.StatusCode != http.StatusAccepted && resp.StatusCode != http.StatusOK {
		fmt.Fprintf(os.Stderr, "Error: API returned status %d: %s\n", resp.StatusCode, string(body))
		os.Exit(1)
	}

	// Parse and display response
	var apiResp APIResponse
	if err := json.Unmarshal(body, &apiResp); err != nil {
		fmt.Printf("Restore requested (ID: %s)\n", checkpointID)
	} else {
		fmt.Printf("Status: %s\n", apiResp.Status)
		fmt.Printf("Checkpoint ID: %s\n", apiResp.CheckpointID)
	}
}
