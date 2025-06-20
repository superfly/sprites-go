package main

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
)

// ExecRequest represents the request payload for the /exec endpoint
type ExecRequest struct {
	Command    []string          `json:"command"`
	Env        map[string]string `json:"env,omitempty"`
	WorkingDir string            `json:"working_dir,omitempty"`
	Timeout    int64             `json:"timeout,omitempty"`
	TTY        bool              `json:"tty,omitempty"`
}

// ExecMessage represents a message from the exec stream
type ExecMessage struct {
	Type     string `json:"type"`
	Data     string `json:"data,omitempty"`
	ExitCode int    `json:"exit_code,omitempty"`
	Error    string `json:"error,omitempty"`
}

func main() {
	var (
		workingDir = flag.String("dir", "", "Working directory for the command")
		timeout    = flag.Duration("timeout", 30*time.Second, "Command timeout")
		tty        = flag.Bool("tty", false, "Allocate a pseudo-TTY")
		envVars    = flag.String("env", "", "Environment variables (KEY=value,KEY2=value2)")
		debug      = flag.Bool("debug", false, "Enable debug output")
	)

	flag.Usage = func() {
		fmt.Fprintf(os.Stderr, "Usage: %s [options] command [args...]\n\n", os.Args[0])
		fmt.Fprintf(os.Stderr, "Execute a command remotely via the sprite-env API.\n\n")
		fmt.Fprintf(os.Stderr, "Environment variables:\n")
		fmt.Fprintf(os.Stderr, "  FLY_APP_NAME         Fly.io app name (required)\n")
		fmt.Fprintf(os.Stderr, "  SPRITE_HTTP_API_TOKEN  API authentication token (required)\n\n")
		fmt.Fprintf(os.Stderr, "Options:\n")
		flag.PrintDefaults()
		fmt.Fprintf(os.Stderr, "\nExamples:\n")
		fmt.Fprintf(os.Stderr, "  %s ls -la\n", os.Args[0])
		fmt.Fprintf(os.Stderr, "  %s -dir /app -env KEY=value,FOO=bar echo hello\n", os.Args[0])
		fmt.Fprintf(os.Stderr, "  %s -timeout 5s curl https://example.com\n", os.Args[0])
	}

	flag.Parse()

	if flag.NArg() == 0 {
		fmt.Fprintf(os.Stderr, "Error: No command specified\n\n")
		flag.Usage()
		os.Exit(1)
	}

	// Get required environment variables
	appName := os.Getenv("FLY_APP_NAME")
	if appName == "" {
		fmt.Fprintf(os.Stderr, "Error: FLY_APP_NAME environment variable not set\n")
		os.Exit(1)
	}

	apiToken := os.Getenv("SPRITE_HTTP_API_TOKEN")
	if apiToken == "" {
		fmt.Fprintf(os.Stderr, "Error: SPRITE_HTTP_API_TOKEN environment variable not set\n")
		os.Exit(1)
	}

	// Parse environment variables
	envMap := make(map[string]string)
	if *envVars != "" {
		pairs := strings.Split(*envVars, ",")
		for _, pair := range pairs {
			parts := strings.SplitN(pair, "=", 2)
			if len(parts) == 2 {
				envMap[parts[0]] = parts[1]
			}
		}
	}

	// Build the request
	req := ExecRequest{
		Command:    flag.Args(),
		Env:        envMap,
		WorkingDir: *workingDir,
		Timeout:    timeout.Nanoseconds(),
		TTY:        *tty,
	}

	// Execute the command
	exitCode := executeCommand(appName, apiToken, req, *debug)
	os.Exit(exitCode)
}

func executeCommand(appName, apiToken string, req ExecRequest, debug bool) int {
	url := fmt.Sprintf("https://%s.fly.dev/exec", appName)

	// Marshal the request
	jsonData, err := json.Marshal(req)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to marshal request: %v\n", err)
		return 1
	}

	if debug {
		fmt.Fprintf(os.Stderr, "Debug: URL: %s\n", url)
		fmt.Fprintf(os.Stderr, "Debug: Request: %s\n", string(jsonData))
	}

	// Create the HTTP request
	httpReq, err := http.NewRequest("POST", url, bytes.NewReader(jsonData))
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create request: %v\n", err)
		return 1
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", apiToken))
	httpReq.Header.Set("Content-Type", "application/json")

	// Make the request
	client := &http.Client{
		Timeout: 0, // No timeout for streaming responses
	}

	resp, err := client.Do(httpReq)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to execute request: %v\n", err)
		return 1
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		fmt.Fprintf(os.Stderr, "Error: API returned status %d: %s\n", resp.StatusCode, string(body))
		return 1
	}

	// Process the streaming response
	return processStream(resp.Body, debug)
}

func processStream(reader io.Reader, debug bool) int {
	scanner := bufio.NewScanner(reader)
	exitCode := 0

	for scanner.Scan() {
		line := scanner.Text()
		if line == "" {
			continue
		}

		if debug {
			fmt.Fprintf(os.Stderr, "Debug: Received: %s\n", line)
		}

		var msg ExecMessage
		if err := json.Unmarshal([]byte(line), &msg); err != nil {
			fmt.Fprintf(os.Stderr, "Error: Failed to parse message: %v\n", err)
			continue
		}

		switch msg.Type {
		case "stdout":
			fmt.Print(msg.Data)
		case "stderr":
			fmt.Fprint(os.Stderr, msg.Data)
		case "exit":
			exitCode = msg.ExitCode
			if debug {
				fmt.Fprintf(os.Stderr, "Debug: Process exited with code %d\n", exitCode)
			}
		case "error":
			fmt.Fprintf(os.Stderr, "Error: %s\n", msg.Error)
			if exitCode == 0 {
				exitCode = 1
			}
		default:
			if debug {
				fmt.Fprintf(os.Stderr, "Debug: Unknown message type: %s\n", msg.Type)
			}
		}
	}

	if err := scanner.Err(); err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to read stream: %v\n", err)
		if exitCode == 0 {
			exitCode = 1
		}
	}

	return exitCode
}
