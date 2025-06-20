package sprite

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

func execCommand(baseURL, token string, args []string) {
	// Create a new flag set for the exec subcommand
	execFlags := flag.NewFlagSet("exec", flag.ExitOnError)

	var (
		workingDir = execFlags.String("dir", "", "Working directory for the command")
		timeout    = execFlags.Duration("timeout", 30*time.Second, "Command timeout")
		tty        = execFlags.Bool("tty", false, "Allocate a pseudo-TTY")
		envVars    = execFlags.String("env", "", "Environment variables (KEY=value,KEY2=value2)")
		help       = execFlags.Bool("h", false, "Show help")
	)

	// Custom usage for exec subcommand
	execFlags.Usage = func() {
		fmt.Fprintf(os.Stderr, "Usage: sprite-client exec [options] command [args...]\n\n")
		fmt.Fprintf(os.Stderr, "Execute a command in the sprite environment.\n\n")
		fmt.Fprintf(os.Stderr, "Options:\n")
		execFlags.PrintDefaults()
		fmt.Fprintf(os.Stderr, "\nExamples:\n")
		fmt.Fprintf(os.Stderr, "  sprite-client exec ls -la\n")
		fmt.Fprintf(os.Stderr, "  sprite-client exec -dir /app echo hello world\n")
		fmt.Fprintf(os.Stderr, "  sprite-client exec -env KEY=value,FOO=bar env\n")
		fmt.Fprintf(os.Stderr, "  sprite-client exec -timeout 5s sleep 10\n")
	}

	// Parse exec flags
	err := execFlags.Parse(args)
	if err != nil {
		os.Exit(1)
	}

	// Check for help flag
	if *help {
		execFlags.Usage()
		os.Exit(0)
	}

	// Get remaining args as command
	cmdArgs := execFlags.Args()
	if len(cmdArgs) == 0 {
		fmt.Fprintf(os.Stderr, "Error: No command specified\n\n")
		execFlags.Usage()
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
		Command:    cmdArgs,
		Env:        envMap,
		WorkingDir: *workingDir,
		Timeout:    timeout.Nanoseconds(),
		TTY:        *tty,
	}

	// Execute the command
	exitCode := executeRemoteCommand(baseURL, token, req)
	os.Exit(exitCode)
}

func executeRemoteCommand(baseURL, token string, req ExecRequest) int {
	url := fmt.Sprintf("%s/exec", baseURL)

	// Marshal the request
	jsonData, err := json.Marshal(req)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to marshal request: %v\n", err)
		return 1
	}

	// Create the HTTP request
	httpReq, err := http.NewRequest("POST", url, bytes.NewReader(jsonData))
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create request: %v\n", err)
		return 1
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", token))
	httpReq.Header.Set("Content-Type", "application/json")

	// Make the request with no timeout for streaming
	client := &http.Client{
		Timeout: 0,
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
	return processExecStream(resp.Body)
}

func processExecStream(reader io.Reader) int {
	scanner := bufio.NewScanner(reader)
	exitCode := 0

	for scanner.Scan() {
		line := scanner.Text()
		if line == "" {
			continue
		}

		var msg ExecMessage
		if err := json.Unmarshal([]byte(line), &msg); err != nil {
			fmt.Fprintf(os.Stderr, "Error: Failed to parse message: %v\n", err)
			continue
		}

		switch msg.Type {
		case "stdout":
			fmt.Println(msg.Data)
		case "stderr":
			fmt.Fprintln(os.Stderr, msg.Data)
		case "exit":
			exitCode = msg.ExitCode
		case "error":
			fmt.Fprintf(os.Stderr, "Error: %s\n", msg.Error)
			if exitCode == 0 {
				exitCode = 1
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
