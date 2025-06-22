package main

import (
	"bytes"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"lib/api"
	"lib/stdcopy"
	"net/http"
	"os"
	"strings"
)

func execCommand(baseURL, token string, args []string) {
	// Create a new flag set for the exec subcommand
	execFlags := flag.NewFlagSet("exec", flag.ExitOnError)

	var (
		workingDir = execFlags.String("dir", "", "Working directory for the command")
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
	var envList []string
	if *envVars != "" {
		pairs := strings.Split(*envVars, ",")
		for _, pair := range pairs {
			envList = append(envList, strings.TrimSpace(pair))
		}
	}

	// Execute using Docker-compatible API
	exitCode := executeDockerExec(baseURL, token, cmdArgs, *workingDir, envList, *tty)
	os.Exit(exitCode)
}

func executeDockerExec(baseURL, token string, cmd []string, workingDir string, env []string, tty bool) int {
	// Step 1: Create exec instance
	createReq := api.DockerExecCreateRequest{
		Cmd:          cmd,
		AttachStdout: true,
		AttachStderr: true,
		AttachStdin:  false,
		Tty:          tty,
		Env:          env,
		WorkingDir:   workingDir,
	}

	createBody, err := json.Marshal(createReq)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to marshal create request: %v\n", err)
		return 1
	}

	// Use a dummy container ID (server ignores it anyway)
	createURL := fmt.Sprintf("%s/containers/sprite/exec", baseURL)
	req, err := http.NewRequest("POST", createURL, bytes.NewReader(createBody))
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create request: %v\n", err)
		return 1
	}

	req.Header.Set("Authorization", fmt.Sprintf("Bearer %s", token))
	req.Header.Set("Content-Type", "application/json")

	client := &http.Client{}
	resp, err := client.Do(req)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create exec instance: %v\n", err)
		return 1
	}

	if resp.StatusCode != http.StatusCreated {
		body, _ := io.ReadAll(resp.Body)
		resp.Body.Close()
		fmt.Fprintf(os.Stderr, "Error: Failed to create exec instance (status %d): %s\n", resp.StatusCode, string(body))
		return 1
	}

	var createResp api.DockerExecCreateResponse
	if err := json.NewDecoder(resp.Body).Decode(&createResp); err != nil {
		resp.Body.Close()
		fmt.Fprintf(os.Stderr, "Error: Failed to decode create response: %v\n", err)
		return 1
	}
	resp.Body.Close()

	execID := createResp.Id

	// Step 2: Start exec instance
	startReq := api.DockerExecStartRequest{
		Detach: false,
		Tty:    tty,
	}

	startBody, err := json.Marshal(startReq)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to marshal start request: %v\n", err)
		return 1
	}

	startURL := fmt.Sprintf("%s/exec/%s/start", baseURL, execID)
	req, err = http.NewRequest("POST", startURL, bytes.NewReader(startBody))
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create start request: %v\n", err)
		return 1
	}

	req.Header.Set("Authorization", fmt.Sprintf("Bearer %s", token))
	req.Header.Set("Content-Type", "application/json")

	// Only request upgrade for non-HTTPS connections (HTTP/1.1)
	// HTTP/2 (used by HTTPS) doesn't support the Upgrade mechanism
	if !strings.HasPrefix(baseURL, "https://") {
		req.Header.Set("Connection", "Upgrade")
		req.Header.Set("Upgrade", "tcp")
	}

	// Use client with no timeout for streaming
	streamClient := &http.Client{Timeout: 0}
	resp, err = streamClient.Do(req)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to start exec instance: %v\n", err)
		return 1
	}
	defer resp.Body.Close()

	// Check if we got upgraded or regular streaming
	if resp.StatusCode == http.StatusSwitchingProtocols {
		// Got upgraded connection - use stdcopy to demultiplex
		_, err := stdcopy.StdCopy(os.Stdout, os.Stderr, resp.Body)
		if err != nil && err != io.EOF {
			fmt.Fprintf(os.Stderr, "Error reading stream: %v\n", err)
		}
	} else if resp.StatusCode == http.StatusOK {
		// Regular streaming - use stdcopy to demultiplex
		_, err := stdcopy.StdCopy(os.Stdout, os.Stderr, resp.Body)
		if err != nil && err != io.EOF {
			fmt.Fprintf(os.Stderr, "Error reading stream: %v\n", err)
		}
	} else {
		body, _ := io.ReadAll(resp.Body)
		fmt.Fprintf(os.Stderr, "Error: Failed to start exec instance (status %d): %s\n", resp.StatusCode, string(body))
		return 1
	}

	// Step 3: Get exit code from inspect
	inspectURL := fmt.Sprintf("%s/exec/%s/json", baseURL, execID)
	req, err = http.NewRequest("GET", inspectURL, nil)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to create inspect request: %v\n", err)
		return 1
	}

	req.Header.Set("Authorization", fmt.Sprintf("Bearer %s", token))

	resp, err = client.Do(req)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to inspect exec instance: %v\n", err)
		return 1
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		fmt.Fprintf(os.Stderr, "Error: Failed to inspect exec instance (status %d): %s\n", resp.StatusCode, string(body))
		return 1
	}

	var inspectResp api.DockerExecInspectResponse
	if err := json.NewDecoder(resp.Body).Decode(&inspectResp); err != nil {
		fmt.Fprintf(os.Stderr, "Error: Failed to decode inspect response: %v\n", err)
		return 1
	}

	return inspectResp.ExitCode
}
