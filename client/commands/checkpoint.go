package commands

import (
	"bufio"
	"bytes"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"net/http"
	"os"
	"strings"
	"time"

	"log/slog"

	"github.com/sprite-env/client/config"
	"github.com/sprite-env/client/format"
	"github.com/sprite-env/lib/api"
)

// CheckpointCommand handles the checkpoint command
func CheckpointCommand(ctx *GlobalContext, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "checkpoint",
		Usage:       "checkpoint <subcommand> [options]",
		Description: "Manage checkpoints",
		FlagSet:     flag.NewFlagSet("checkpoint", flag.ContinueOnError),
		Examples: []string{
			"sprite checkpoint create",
			"sprite checkpoint list",
			"sprite checkpoint info <checkpoint-id>",
			"sprite checkpoint list --history VERSION",
		},
	}

	// Set up sprite flags for the main checkpoint command
	flags := NewSpriteFlags(cmd.FlagSet)

	// Custom usage to show subcommands
	cmd.FlagSet.Usage = func() {
		fmt.Fprintf(os.Stderr, "%s\n\n", cmd.Description)
		fmt.Fprintf(os.Stderr, "Usage:\n  sprite %s\n\n", cmd.Usage)
		fmt.Fprintf(os.Stderr, "Subcommands:\n")
		fmt.Fprintf(os.Stderr, "  create    Create a new checkpoint\n")
		fmt.Fprintf(os.Stderr, "  list      List all checkpoints\n")
		fmt.Fprintf(os.Stderr, "  info      Show information about a specific checkpoint\n\n")
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
	}

	// Parse flags to get org/sprite overrides
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	// Ensure we have an org and sprite
	org, spriteName, err := EnsureOrgAndSprite(ctx.ConfigMgr, flags.Org, flags.Sprite)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}

	if len(remainingArgs) < 1 {
		fmt.Fprintf(os.Stderr, "Error: checkpoint requires a subcommand\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	subcommand := remainingArgs[0]
	subArgs := remainingArgs[1:]

	switch subcommand {
	case "create":
		checkpointCreateCommand(ctx.ConfigMgr, org, spriteName, subArgs)
	case "list":
		checkpointListCommandWithFlags(ctx.ConfigMgr, org, spriteName, subArgs)
	case "info":
		if len(subArgs) < 1 {
			fmt.Fprintf(os.Stderr, "Error: checkpoint info requires a checkpoint ID\n\n")
			cmd.FlagSet.Usage()
			os.Exit(1)
		}
		checkpointInfoCommand(ctx.ConfigMgr, org, spriteName, subArgs)
	default:
		fmt.Fprintf(os.Stderr, "Error: Unknown checkpoint subcommand '%s'\n\n", subcommand)
		cmd.FlagSet.Usage()
		os.Exit(1)
	}
}

func checkpointCreateCommand(cfg *config.Manager, org *config.Organization, spriteName string, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "checkpoint create",
		Usage:       "checkpoint create",
		Description: "Create a new checkpoint",
		FlagSet:     flag.NewFlagSet("checkpoint create", flag.ContinueOnError),
	}

	// Set up flags
	_ = NewGlobalFlags(cmd.FlagSet)

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	if len(remainingArgs) != 0 {
		fmt.Fprintf(os.Stderr, "Error: checkpoint create takes no arguments\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	// Create empty request (backward compatible)
	req := api.CheckpointRequest{}

	jsonData, err := json.Marshal(req)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create request: %v\n", err)
		os.Exit(1)
	}

	// Build the URL
	var url string
	if spriteName != "" && org.Name != "env" {
		// Use sprite proxy endpoint
		url = buildSpriteProxyURL(org, spriteName, "/checkpoint")
	} else {
		// Use direct endpoint for backward compatibility
		url = fmt.Sprintf("%s/checkpoint", org.URL)
	}

	httpReq, err := http.NewRequest("POST", url, bytes.NewReader(jsonData))
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create HTTP request: %v\n", err)
		os.Exit(1)
	}

	token, err := org.GetTokenWithKeyringDisabled(cfg.IsKeyringDisabled())
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to get auth token: %v\n", err)
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

func checkpointListCommandWithFlags(cfg *config.Manager, org *config.Organization, spriteName string, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "checkpoint list",
		Usage:       "checkpoint list [options]",
		Description: "List all checkpoints",
		FlagSet:     flag.NewFlagSet("checkpoint list", flag.ContinueOnError),
	}

	// Set up flags
	_ = NewGlobalFlags(cmd.FlagSet)
	historyFilter := cmd.FlagSet.String("history", "", "Filter by history version")

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	if len(remainingArgs) > 0 {
		fmt.Fprintf(os.Stderr, "Error: checkpoint list takes no arguments\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	checkpointListCommand(cfg, org, spriteName, *historyFilter)
}

func checkpointListCommand(cfg *config.Manager, org *config.Organization, spriteName string, historyFilter string) {
	// Build the URL
	var url string
	if spriteName != "" && org.Name != "env" {
		// Use sprite proxy endpoint
		url = buildSpriteProxyURL(org, spriteName, "/checkpoints")
	} else {
		// Use direct endpoint for backward compatibility
		url = fmt.Sprintf("%s/checkpoints", org.URL)
	}

	if historyFilter != "" {
		url += fmt.Sprintf("?history=%s", historyFilter)
	}

	httpReq, err := http.NewRequest("GET", url, nil)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create HTTP request: %v\n", err)
		os.Exit(1)
	}

	token, err := org.GetTokenWithKeyringDisabled(cfg.IsKeyringDisabled())
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to get auth token: %v\n", err)
		os.Exit(1)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", token))

	// Debug log the request
	slog.Debug("Checkpoint list request",
		"url", url,
		"org", org.Name,
		"sprite", spriteName,
		"authorization", fmt.Sprintf("Bearer %s", truncateToken(token)))

	client := &http.Client{Timeout: 30 * time.Second}
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

	// Check if we have stats available
	hasStats := false
	hasCurrent := false
	for _, cp := range checkpoints {
		if cp.FileCount > 0 || cp.TotalSize > 0 {
			hasStats = true
		}
		if cp.ID == "Current" {
			hasCurrent = true
		}
	}

	// Display header based on available data
	if hasStats {
		fmt.Printf("%-25s %-20s %10s %10s %15s %s\n", "ID", "CREATED", "FILES", "DIRS", "SIZE", "DIVERGENCE")
		fmt.Printf("%-25s %-20s %10s %10s %15s %s\n", 
			strings.Repeat("-", 25), 
			strings.Repeat("-", 20),
			strings.Repeat("-", 10),
			strings.Repeat("-", 10),
			strings.Repeat("-", 15),
			strings.Repeat("-", 20))
	} else {
		fmt.Printf("%-30s %s\n", "ID", "CREATED")
		fmt.Printf("%-30s %s\n", strings.Repeat("-", 30), strings.Repeat("-", 25))
	}

	for _, cp := range checkpoints {
		created := cp.CreateTime.Format("2006-01-02 15:04:05")
		
		// Format the ID for display
		displayID := cp.ID
		if cp.ID == "Current" {
			displayID = "→ Current (active)"
		}
		
		if hasStats {
			sizeStr := "-"
			if cp.TotalSize > 0 {
				sizeStr = formatSize(cp.TotalSize)
			}
			
			filesStr := "-"
			if cp.FileCount > 0 {
				filesStr = fmt.Sprintf("%d", cp.FileCount)
			}
			
			dirsStr := "-"
			if cp.DirCount > 0 {
				dirsStr = fmt.Sprintf("%d", cp.DirCount)
			}
			
			divergence := ""
			if cp.DivergenceIndicator != "" {
				divergence = cp.DivergenceIndicator
				if cp.FilesDiff != 0 {
					divergence += fmt.Sprintf(" (%+d files)", cp.FilesDiff)
				}
			}
			
			fmt.Printf("%-25s %-20s %10s %10s %15s %s\n", 
				displayID, created, filesStr, dirsStr, sizeStr, divergence)
		} else {
			fmt.Printf("%-30s %s\n", displayID, created)
		}
	}
	
	// Add a note about the current state
	if hasCurrent {
		fmt.Println("\n→ Current represents the active working state of your environment")
	}
}

// formatSize formats bytes to human-readable format
func formatSize(bytes int64) string {
	const unit = 1024
	if bytes < unit {
		return fmt.Sprintf("%d B", bytes)
	}
	div, exp := int64(unit), 0
	for n := bytes / unit; n >= unit; n /= unit {
		div *= unit
		exp++
	}
	return fmt.Sprintf("%.2f %cB", float64(bytes)/float64(div), "KMGTPE"[exp])
}

func checkpointInfoCommand(cfg *config.Manager, org *config.Organization, spriteName string, args []string) {
	if len(args) != 1 {
		fmt.Fprintf(os.Stderr, "Error: checkpoint info requires exactly one argument (checkpoint ID)\n")
		fmt.Fprintf(os.Stderr, "Usage: sprite checkpoint info <checkpoint-id>\n")
		os.Exit(1)
	}

	checkpointID := args[0]

	// Build the URL
	var url string
	if spriteName != "" && org.Name != "env" {
		// Use sprite proxy endpoint
		url = buildSpriteProxyURL(org, spriteName, fmt.Sprintf("/checkpoints/%s", checkpointID))
	} else {
		// Use direct endpoint for backward compatibility
		url = fmt.Sprintf("%s/checkpoints/%s", org.URL, checkpointID)
	}

	httpReq, err := http.NewRequest("GET", url, nil)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create HTTP request: %v\n", err)
		os.Exit(1)
	}

	token, err := org.GetTokenWithKeyringDisabled(cfg.IsKeyringDisabled())
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to get auth token: %v\n", err)
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

// RestoreCommand handles the restore command
func RestoreCommand(ctx *GlobalContext, args []string) {
	// Create command structure
	cmd := &Command{
		Name:        "restore",
		Usage:       "restore [options] <checkpoint-id>",
		Description: "Restore from a checkpoint",
		FlagSet:     flag.NewFlagSet("restore", flag.ContinueOnError),
		Examples: []string{
			"sprite restore my-checkpoint-id",
			"sprite restore -o myorg -s mysprite checkpoint-123",
		},
	}

	// Set up flags
	flags := NewSpriteFlags(cmd.FlagSet)

	// Parse flags
	remainingArgs, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	if len(remainingArgs) != 1 {
		fmt.Fprintf(os.Stderr, "Error: restore requires exactly one argument (checkpoint ID)\n\n")
		cmd.FlagSet.Usage()
		os.Exit(1)
	}

	checkpointID := remainingArgs[0]

	// Ensure we have an org and sprite
	org, spriteName, err := EnsureOrgAndSprite(ctx.ConfigMgr, flags.Org, flags.Sprite)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}

	if spriteName != "" {
		fmt.Println(format.ContextSprite(format.GetOrgDisplayName(org.Name, org.URL), fmt.Sprintf("Restoring checkpoint %s for sprite", format.Command(checkpointID)), spriteName))
		fmt.Println()
	}

	// Build the URL
	var url string
	if spriteName != "" && org.Name != "env" {
		// Use sprite proxy endpoint
		url = buildSpriteProxyURL(org, spriteName, fmt.Sprintf("/checkpoints/%s/restore", checkpointID))
	} else {
		// Use direct endpoint for backward compatibility
		url = fmt.Sprintf("%s/checkpoints/%s/restore", org.URL, checkpointID)
	}

	// Debug log the request
	slog.Debug("Restore request",
		"url", url,
		"org", org.Name,
		"sprite", spriteName,
		"checkpointID", checkpointID)

	httpReq, err := http.NewRequest("POST", url, nil)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create HTTP request: %v\n", err)
		os.Exit(1)
	}

	token, err := org.GetTokenWithKeyringDisabled(ctx.ConfigMgr.IsKeyringDisabled())
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to get auth token: %v\n", err)
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
		}
	}

	if err := scanner.Err(); err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to read stream: %v\n", err)
		return 1
	}

	// If we had errors but no specific exit code, return 1
	if hasError && exitCode == 0 {
		return 1
	}

	return exitCode
}
