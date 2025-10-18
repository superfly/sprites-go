package tests

import (
	"bytes"
	"fmt"
	"testing"
	"time"

	sprites "github.com/superfly/sprites-go"
)

// TestExecTTYWithStdin verifies that stdin is delivered over the WebSocket in TTY mode
// using the exact same flow as the Go SDK. It connects to /v1/sprites/:name/exec and
// writes a line to stdin, expecting the process to echo it back.
func TestExecTTYWithStdin(t *testing.T) {
	_, cancel := SetTestDeadlineWithTimeout(t, 45*time.Second)
	defer cancel()

	requireDockerTest(t)
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	testDir := SetupTestEnvironment(t)

	// Configure and start the system with API enabled
	config := TestConfig(testDir)
	SetupTestPorts(t, config)

	sys, cleanup, err := TestSystem(t, config)
	defer cleanup()
	if err != nil {
		t.Fatalf("Failed to create system: %v", err)
	}

	if err := sys.Start(); err != nil {
		t.Fatalf("Failed to start system: %v", err)
	}

	// Ensure process is running so /exec passes middleware
	if err := sys.WhenProcessRunning(t.Context()); err != nil {
		t.Fatalf("Process did not start: %v", err)
	}

	// Build SDK client pointing at this system's API
	baseURL := fmt.Sprintf("http://%s", config.APIListenAddr)
	client := sprites.New(config.APIToken, sprites.WithBaseURL(baseURL))
	sprite := client.Sprite("local-test-sprite")

	// Command reads one line and echoes it back
	cmd := sprite.Command("bash", "-lc", "read -r line; echo You typed: $line")
	cmd.SetTTY(true)

	// Provide stdin and capture stdout
	stdin := bytes.NewBufferString("exit\n")
	var stdout bytes.Buffer
	cmd.Stdin = stdin
	cmd.Stdout = &stdout

	// Start and wait
	if err := cmd.Run(); err != nil {
		t.Fatalf("exec run failed: %v", err)
	}

	// Verify stdout contains the echoed input
	if !containsStr(stdout.String(), "You typed: exit") {
		t.Fatalf("stdout did not contain expected echo. got=%q", stdout.String())
	}
}
