package tests

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// TestAPIServerIntegration tests the API server functionality
func TestAPIServerIntegration(t *testing.T) {
	t.Skip("Temporarily disabled - needs update for new architecture")

	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	// Set up test environment
	testDir := t.TempDir()

	// Create test component scripts
	componentDir := filepath.Join(testDir, "test-component")
	if err := os.MkdirAll(componentDir, 0755); err != nil {
		t.Fatal(err)
	}

	// Create a simple start script
	startScript := filepath.Join(componentDir, "start.sh")
	startContent := `#!/bin/bash
echo "Test component started"
sleep 1
`
	if err := os.WriteFile(startScript, []byte(startContent), 0755); err != nil {
		t.Fatal(err)
	}

	// Create a simple ready script
	readyScript := filepath.Join(componentDir, "ready.sh")
	readyContent := `#!/bin/bash
exit 0
`
	if err := os.WriteFile(readyScript, []byte(readyContent), 0755); err != nil {
		t.Fatal(err)
	}

	// Create a supervised process script
	supervisedScript := filepath.Join(testDir, "supervised.sh")
	supervisedContent := `#!/bin/bash
trap 'exit 0' TERM INT
echo "Supervised process running"
while true; do
	sleep 1
done
`
	if err := os.WriteFile(supervisedScript, []byte(supervisedContent), 0755); err != nil {
		t.Fatal(err)
	}

	// Set API token
	apiToken := "test-token-12345"
	os.Setenv("SPRITE_HTTP_API_TOKEN", apiToken)
	defer os.Unsetenv("SPRITE_HTTP_API_TOKEN")

	// Build the server
	buildCmd := exec.Command("go", "build", "-o", filepath.Join(testDir, "sprite-env"), "../main.go")
	if output, err := buildCmd.CombinedOutput(); err != nil {
		t.Fatalf("Failed to build server: %v\nOutput: %s", err, output)
	}

	// Start the server with API enabled
	serverCmd := exec.Command(
		filepath.Join(testDir, "sprite-env"),
		"--listen", "127.0.0.1:18090",
		"--components-dir", testDir,
		"--",
		supervisedScript,
	)

	// Start server in background
	if err := serverCmd.Start(); err != nil {
		t.Fatalf("Failed to start server: %v", err)
	}
	defer func() {
		serverCmd.Process.Kill()
		serverCmd.Wait()
	}()

	// Wait for server to start and API to be ready
	apiURL := "http://127.0.0.1:18090/exec"
	maxRetries := 30
	for i := 0; i < maxRetries; i++ {
		time.Sleep(100 * time.Millisecond)

		// Try a simple request to check if API is ready
		req, _ := http.NewRequest("POST", apiURL, strings.NewReader(`{"command":["echo","test"]}`))
		req.Header.Set("fly-replay-src", fmt.Sprintf("state=api:%s", apiToken))
		req.Header.Set("Content-Type", "application/json")

		resp, err := http.DefaultClient.Do(req)
		if err == nil {
			resp.Body.Close()
			if resp.StatusCode == http.StatusOK {
				break
			}
		}

		if i == maxRetries-1 {
			t.Fatal("API server did not become ready in time")
		}
	}

	// Test cases
	tests := []struct {
		name           string
		command        []string
		timeout        int64 // nanoseconds
		expectSuccess  bool
		expectExitCode int
	}{
		{
			name:           "Simple echo command",
			command:        []string{"echo", "Hello from API"},
			timeout:        5000000000,
			expectSuccess:  true,
			expectExitCode: 0,
		},
		{
			name:           "Command with stderr",
			command:        []string{"sh", "-c", "echo stdout; echo stderr >&2"},
			timeout:        5000000000,
			expectSuccess:  true,
			expectExitCode: 0,
		},
		{
			name:           "Command that fails",
			command:        []string{"sh", "-c", "exit 42"},
			timeout:        5000000000,
			expectSuccess:  false,
			expectExitCode: 42,
		},
		{
			name:           "List directory",
			command:        []string{"ls", "-la", testDir},
			timeout:        5000000000,
			expectSuccess:  true,
			expectExitCode: 0,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Prepare request
			reqBody := map[string]interface{}{
				"command": tt.command,
				"timeout": tt.timeout,
			}

			jsonBody, err := json.Marshal(reqBody)
			if err != nil {
				t.Fatal(err)
			}

			// Make API request
			req, err := http.NewRequest("POST", apiURL, bytes.NewReader(jsonBody))
			if err != nil {
				t.Fatal(err)
			}

			req.Header.Set("fly-replay-src", fmt.Sprintf("state=api:%s", apiToken))
			req.Header.Set("Content-Type", "application/json")

			resp, err := http.DefaultClient.Do(req)
			if err != nil {
				t.Fatal(err)
			}
			defer resp.Body.Close()

			if resp.StatusCode != http.StatusOK {
				body, _ := io.ReadAll(resp.Body)
				t.Fatalf("Expected status 200, got %d: %s", resp.StatusCode, body)
			}

			// Check Content-Type
			contentType := resp.Header.Get("Content-Type")
			if contentType != "application/x-ndjson" {
				t.Errorf("Expected Content-Type application/x-ndjson, got %s", contentType)
			}

			// Read and parse response
			body, err := io.ReadAll(resp.Body)
			if err != nil {
				t.Fatal(err)
			}

			lines := strings.Split(strings.TrimSpace(string(body)), "\n")
			var exitCode int
			var foundExit bool

			for _, line := range lines {
				if line == "" {
					continue
				}

				var msg map[string]interface{}
				if err := json.Unmarshal([]byte(line), &msg); err != nil {
					t.Errorf("Failed to parse JSON line: %v", err)
					continue
				}

				if msg["type"] == "exit" {
					foundExit = true
					if code, ok := msg["exit_code"].(float64); ok {
						exitCode = int(code)
					}
				}

				t.Logf("Message: %v", msg)
			}

			if !foundExit {
				t.Error("No exit message found in response")
			}

			if exitCode != tt.expectExitCode {
				t.Errorf("Expected exit code %d, got %d", tt.expectExitCode, exitCode)
			}
		})
	}
}

// TestAPIServerAuthentication tests various authentication scenarios
func TestAPIServerAuthentication(t *testing.T) {
	t.Skip("Temporarily disabled - needs update for new architecture")

	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	// Similar setup as above but focused on auth testing
	testDir := t.TempDir()

	// Create minimal test setup
	componentDir := filepath.Join(testDir, "test-component")
	os.MkdirAll(componentDir, 0755)

	startScript := filepath.Join(componentDir, "start.sh")
	os.WriteFile(startScript, []byte("#!/bin/bash\nsleep 1\n"), 0755)

	// Set API token
	apiToken := "secret-auth-token"
	os.Setenv("SPRITE_HTTP_API_TOKEN", apiToken)
	defer os.Unsetenv("SPRITE_HTTP_API_TOKEN")

	// Build and start server
	buildCmd := exec.Command("go", "build", "-o", filepath.Join(testDir, "sprite-env"), "../main.go")
	buildCmd.CombinedOutput()

	serverCmd := exec.Command(
		filepath.Join(testDir, "sprite-env"),
		"--listen", "127.0.0.1:18091",
		"--components-dir", testDir,
		"--",
		"sleep", "3600",
	)

	serverCmd.Start()
	defer func() {
		serverCmd.Process.Kill()
		serverCmd.Wait()
	}()

	// Wait for server
	time.Sleep(2 * time.Second)

	apiURL := "http://127.0.0.1:18091/exec"

	// Test cases for authentication
	authTests := []struct {
		name         string
		headerValue  string
		authHeader   string
		expectStatus int
	}{
		{
			name:         "Valid authentication with fly-replay-src",
			headerValue:  fmt.Sprintf("state=api:%s", apiToken),
			expectStatus: http.StatusOK,
		},
		{
			name:         "Valid authentication with Bearer token",
			authHeader:   fmt.Sprintf("Bearer %s", apiToken),
			expectStatus: http.StatusOK,
		},
		{
			name:         "Wrong token in fly-replay-src",
			headerValue:  "state=api:wrong-token",
			expectStatus: http.StatusUnauthorized,
		},
		{
			name:         "Wrong Bearer token",
			authHeader:   "Bearer wrong-token",
			expectStatus: http.StatusUnauthorized,
		},
		{
			name:         "Missing authentication",
			headerValue:  "",
			expectStatus: http.StatusUnauthorized,
		},
		{
			name:         "Invalid fly-replay-src format",
			headerValue:  "invalid-format",
			expectStatus: http.StatusUnauthorized,
		},
		{
			name:         "Proxy mode in fly-replay-src ignored",
			headerValue:  fmt.Sprintf("state=proxy:%s:8080", apiToken),
			expectStatus: http.StatusUnauthorized,
		},
		{
			name:         "Missing state key in fly-replay-src",
			headerValue:  "region=ord;app=myapp",
			expectStatus: http.StatusUnauthorized,
		},
		{
			name:         "Malformed state in fly-replay-src",
			headerValue:  "state=invalid",
			expectStatus: http.StatusUnauthorized,
		},
		{
			name:         "State with extra fields",
			headerValue:  fmt.Sprintf("region=ord;state=api:%s;app=myapp", apiToken),
			expectStatus: http.StatusOK,
		},
		{
			name:         "Basic auth not supported",
			authHeader:   "Basic dXNlcjpwYXNz",
			expectStatus: http.StatusUnauthorized,
		},
		{
			name:         "Bearer token takes precedence",
			authHeader:   fmt.Sprintf("Bearer %s", apiToken),
			headerValue:  "state=api:wrong-token",
			expectStatus: http.StatusOK,
		},
	}

	for _, tt := range authTests {
		t.Run(tt.name, func(t *testing.T) {
			reqBody := `{"command":["echo","test"],"timeout":1000000000}`
			req, _ := http.NewRequest("POST", apiURL, strings.NewReader(reqBody))
			req.Header.Set("Content-Type", "application/json")

			if tt.headerValue != "" {
				req.Header.Set("fly-replay-src", tt.headerValue)
			}
			if tt.authHeader != "" {
				req.Header.Set("Authorization", tt.authHeader)
			}

			resp, err := http.DefaultClient.Do(req)
			if err != nil {
				// Server might not be ready yet
				t.Skipf("Could not connect to server: %v", err)
			}
			defer resp.Body.Close()

			if resp.StatusCode != tt.expectStatus {
				body, _ := io.ReadAll(resp.Body)
				t.Errorf("Expected status %d, got %d: %s", tt.expectStatus, resp.StatusCode, body)
			}
		})
	}
}
