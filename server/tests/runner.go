package tests

import (
	"bufio"
	"context"
	"encoding/json"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"testing"
	"time"
)

type ExpectedState struct {
	OverallState string            `json:"overallState,omitempty"`
	ComponentSet ComponentSetState `json:"componentSet,omitempty"`
	ProcessState interface{}       `json:"processState,omitempty"` // Can be string or []string
}

type ComponentSetState struct {
	State      string              `json:"state"`
	Components map[string][]string `json:"components"`
}

type ExpectedStates struct {
	States []ExpectedState `json:"states"`
}

type StateChange struct {
	Vars map[string]interface{} `json:"vars"`
}

type TraceOutput struct {
	Vars map[string]interface{} `json:"vars"`
}

func RunTests(t *testing.T) {
	testScriptsDir := os.Getenv("TSCRIPTS_DIR")
	if testScriptsDir == "" {
		t.Fatalf("TSCRIPTS_DIR environment variable not set. Please run 'make test'.")
	}
	testDirs, err := filepath.Glob(filepath.Join(testScriptsDir, "*/"))
	if err != nil {
		t.Fatalf("Failed to find test directories: %v", err)
	}
	if len(testDirs) == 0 {
		t.Fatalf("No test directories found in %s/*/", testScriptsDir)
	}
	t.Logf("Found test directories: %v", testDirs)

	// Run tests for each directory
	for _, dir := range testDirs {
		dir = filepath.Clean(dir)
		t.Run(filepath.Base(dir), func(t *testing.T) {
			runTest(t, dir)
		})
	}
}

func runTest(t *testing.T, dir string) {
	t.Logf("Running test for directory: %s", dir)

	// Read expected states
	expectedStatesPath := filepath.Join(dir, "expected-states.json")
	expectedStatesData, err := os.ReadFile(expectedStatesPath)
	if err != nil {
		t.Fatalf("Failed to read expected states: %v", err)
	}

	var expectedStates ExpectedStates
	if err := json.Unmarshal(expectedStatesData, &expectedStates); err != nil {
		t.Fatalf("Failed to parse expected states: %v", err)
	}

	// Create command to run the server
	cmd := exec.Command("../tmp/sprite-env", "-debug", "-tla-trace", "-test-dir", dir, "--", filepath.Join(dir, "supervised-process.sh"))
	t.Logf("Running command: %v", cmd.Args)

	// Create pipes for stdout and stderr
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		t.Fatalf("Failed to create stdout pipe: %v", err)
	}
	stderr, err := cmd.StderrPipe()
	if err != nil {
		t.Fatalf("Failed to create stderr pipe: %v", err)
	}

	// Start the process
	if err := cmd.Start(); err != nil {
		t.Fatalf("Failed to start process: %v", err)
	}
	t.Logf("Started process with PID: %d", cmd.Process.Pid)

	// Create context for goroutine cancellation
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	// Create channels for state changes and completion
	stateChanges := make(chan StateChange, 100)
	stopChan := make(chan struct{})
	var stopOnce sync.Once
	stderrDone := make(chan struct{})
	stdoutDone := make(chan struct{})

	// Start goroutine to scan stderr for state changes
	go func() {
		defer close(stderrDone)
		defer close(stateChanges)
		scanner := bufio.NewScanner(stderr)
		for scanner.Scan() {
			select {
			case <-ctx.Done():
				return
			default:
			}
			line := scanner.Text()
			// Try to parse the line as JSON
			var vars map[string]interface{}
			if err := json.Unmarshal([]byte(line), &vars); err == nil {
				select {
				case <-ctx.Done():
					return
				default:
					t.Logf("Raw TLA trace: %s", line)
					if strings.Contains(line, "\"processState\":\"Running\"") {
						// Use stopOnce to ensure this only happens once
						stopOnce.Do(func() {
							t.Logf("Found processState Running, waiting 2 seconds before shutdown")
							time.Sleep(2 * time.Second)
							close(stopChan)
						})
					}
					t.Logf("Unmarshaled trace: %+v", vars)
					stateChanges <- StateChange{Vars: vars}
				}
			} else {
				select {
				case <-ctx.Done():
					return
				default:
					t.Logf("STDERR: %s", line)
				}
			}
		}
		if err := scanner.Err(); err != nil {
			select {
			case <-ctx.Done():
				return
			default:
				t.Fatalf("Error reading stderr: %v", err)
			}
		}
	}()

	// Start goroutine to scan stdout for debug logs
	go func() {
		defer close(stdoutDone)
		scanner := bufio.NewScanner(stdout)
		for scanner.Scan() {
			select {
			case <-ctx.Done():
				return
			default:
				t.Logf("STDOUT: %s", scanner.Text())
			}
		}
		if err := scanner.Err(); err != nil {
			select {
			case <-ctx.Done():
				return
			default:
				t.Fatalf("Error reading stdout: %v", err)
			}
		}
	}()

	// Wait for completion signal
	t.Logf("Waiting for completion signal...")
	<-stopChan

	// Send SIGTERM to process
	t.Logf("Sending SIGTERM to process")
	if err := cmd.Process.Signal(os.Interrupt); err != nil {
		t.Fatalf("Failed to send SIGTERM: %v", err)
	}

	// Wait for process to exit
	t.Logf("Waiting for process to exit")
	if err := cmd.Wait(); err != nil {
		// Check if it's an exit error with a signal-based exit code
		if exitError, ok := err.(*exec.ExitError); ok {
			exitCode := exitError.ExitCode()
			// Accept signal-based exit codes (128 + signal number)
			// SIGINT = 130 (128 + 2), SIGTERM = 143 (128 + 15)
			if exitCode == 130 || exitCode == 143 {
				t.Logf("Process exited with signal-based exit code %d (acceptable)", exitCode)
			} else {
				t.Fatalf("Process exited with unexpected exit code %d: %v", exitCode, err)
			}
		} else {
			t.Fatalf("Process exited with error: %v", err)
		}
	} else {
		t.Logf("Process exited successfully with code 0")
	}

	// Wait specifically for stderr and stdout goroutines to finish
	t.Logf("Waiting for stderr goroutine to finish")
	select {
	case <-stderrDone:
		t.Logf("Stderr goroutine finished")
	case <-time.After(1 * time.Second):
		t.Logf("Stderr goroutine didn't finish within timeout, proceeding anyway")
	}

	t.Logf("Waiting for stdout goroutine to finish")
	select {
	case <-stdoutDone:
		t.Logf("Stdout goroutine finished")
	case <-time.After(1 * time.Second):
		t.Logf("Stdout goroutine didn't finish within timeout, proceeding anyway")
	}

	// Verify state changes against expected states
	verifyStateChanges(t, expectedStates.States, stateChanges)
}

// matchesExpectedState checks if the current state matches an expected state
func matchesExpectedState(overallState, componentSetState, processState, dbState, fsState string, expected ExpectedState) bool {
	// Check overall state
	if overallState != expected.OverallState {
		return false
	}

	// Check component set state
	if componentSetState != expected.ComponentSet.State {
		return false
	}

	// Check process state (can be string or array)
	processStateValid := false
	switch ps := expected.ProcessState.(type) {
	case string:
		processStateValid = (processState == ps)
	case []interface{}:
		for _, validState := range ps {
			if str, ok := validState.(string); ok && processState == str {
				processStateValid = true
				break
			}
		}
	case []string:
		for _, validState := range ps {
			if processState == validState {
				processStateValid = true
				break
			}
		}
	case nil:
		processStateValid = true
	}
	if !processStateValid {
		return false
	}

	// Check DB state
	if dbStates, ok := expected.ComponentSet.Components["DB"]; ok && len(dbStates) > 0 {
		dbStateValid := false
		for _, validState := range dbStates {
			if dbState == validState {
				dbStateValid = true
				break
			}
		}
		if !dbStateValid {
			return false
		}
	}

	// Check FS state
	if fsStates, ok := expected.ComponentSet.Components["FS"]; ok && len(fsStates) > 0 {
		fsStateValid := false
		for _, validState := range fsStates {
			if fsState == validState {
				fsStateValid = true
				break
			}
		}
		if !fsStateValid {
			return false
		}
	}

	return true
}

func verifyStateChanges(t *testing.T, expectedStates []ExpectedState, actual chan StateChange) {
	currentStateIndex := 0
	stateChangesSeen := 0

	for stateChange := range actual {
		stateChangesSeen++

		// Safely extract state fields, failing if missing or nil
		overallState, ok := stateChange.Vars["overallState"].(string)
		if !ok {
			t.Fatalf("State change missing required field: overallState")
		}
		componentSetState, ok := stateChange.Vars["componentSetState"].(string)
		if !ok {
			t.Fatalf("State change missing required field: componentSetState")
		}
		dbState, ok := stateChange.Vars["dbState"].(string)
		if !ok {
			t.Fatalf("State change missing required field: dbState")
		}
		fsState, ok := stateChange.Vars["fsState"].(string)
		if !ok {
			t.Fatalf("State change missing required field: fsState")
		}
		processState, ok := stateChange.Vars["processState"].(string)
		if !ok {
			t.Fatalf("State change missing required field: processState")
		}

		// Check if we should advance to next expected state
		// Look ahead to see if this state matches the next expected state
		if currentStateIndex < len(expectedStates)-1 {
			nextExpected := expectedStates[currentStateIndex+1]
			if matchesExpectedState(overallState, componentSetState, processState, dbState, fsState, nextExpected) {
				currentStateIndex++
			}
		}

		if currentStateIndex >= len(expectedStates) {
			t.Fatalf("Unexpected state change after all expected states: %v", stateChange.Vars)
		}

		expected := expectedStates[currentStateIndex]

		// Validate using the same logic as advancement
		if !matchesExpectedState(overallState, componentSetState, processState, dbState, fsState, expected) {
			// Only log specific errors if validation fails
			if overallState != expected.OverallState {
				t.Errorf("Expected overall state %s, got %s", expected.OverallState, overallState)
			}
			if componentSetState != expected.ComponentSet.State {
				t.Errorf("Expected component set state %s, got %s", expected.ComponentSet.State, componentSetState)
			}
			t.Errorf("Expected process state %v, got %s", expected.ProcessState, processState)
			if dbStates, ok := expected.ComponentSet.Components["DB"]; ok {
				t.Errorf("Expected DB state to be one of %v, got %s", dbStates, dbState)
			}
			if fsStates, ok := expected.ComponentSet.Components["FS"]; ok {
				t.Errorf("Expected FS state to be one of %v, got %s", fsStates, fsState)
			}
		}

		// Continue processing
	}

	if currentStateIndex < len(expectedStates)-1 {
		t.Fatalf("Did not see all expected states. Saw %d of %d states", currentStateIndex+1, len(expectedStates))
	}

	t.Logf("Verified %d state changes against %d expected states", stateChangesSeen, len(expectedStates))
}
