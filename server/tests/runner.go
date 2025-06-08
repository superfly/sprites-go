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
		// Skip _shared directory
		if filepath.Base(dir) == "_shared" {
			continue
		}
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

	// Get absolute path to sprite-env binary
	spriteEnvPath, err := filepath.Abs("../tmp/sprite-env")
	if err != nil {
		t.Fatalf("Failed to get absolute path to sprite-env: %v", err)
	}

	// Get absolute path to supervised process script
	supervisedProcessPath, err := filepath.Abs(filepath.Join(dir, "supervised-process.sh"))
	if err != nil {
		t.Fatalf("Failed to get absolute path to supervised process script: %v", err)
	}

	// Create command to run the server with absolute paths
	cmd := exec.Command(spriteEnvPath, "-tla-trace", "-debug", "-test-dir", dir, "--", supervisedProcessPath)
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

	// Create trace file
	testName := filepath.Base(dir)
	// Create tmp directory if it doesn't exist
	if err := os.MkdirAll("tmp", 0755); err != nil {
		t.Fatalf("Failed to create tmp directory: %v", err)
	}
	traceFile, err := os.Create(filepath.Join("tmp", testName+".txt"))
	if err != nil {
		t.Fatalf("Failed to create trace file: %v", err)
	}
	defer traceFile.Close()

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
					if strings.Contains(line, "\"processState\":\"Running\"") {
						// Use stopOnce to ensure this only happens once
						stopOnce.Do(func() {
							time.Sleep(2 * time.Second)
							close(stopChan)
						})
					}
					stateChanges <- StateChange{Vars: vars}
					// Write state change to trace file
					if _, err := traceFile.WriteString(line + "\n"); err != nil {
						t.Errorf("Failed to write to trace file: %v", err)
					}
				}
			} else {
				// Forward all output, including debug
				os.Stderr.WriteString(line + "\n")
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
				line := scanner.Text()
				// Forward all output, including debug
				os.Stdout.WriteString(line + "\n")
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

// verifyStateChanges verifies that the actual state changes match the expected states
func verifyStateChanges(t *testing.T, expectedStates []ExpectedState, actual chan StateChange) {
	var stateChanges []StateChange
	for change := range actual {
		stateChanges = append(stateChanges, change)
	}

	t.Logf("=== COLLECTED TRACES ===")
	t.Logf("Total traces captured: %d", len(stateChanges))
	for i, change := range stateChanges {
		vars := change.Vars
		t.Logf("Trace %d: overallState=%s, componentSetState=%s, processState=%s, dbState=%s, fsState=%s",
			i, vars["overallState"], vars["componentSetState"], vars["processState"], vars["dbState"], vars["fsState"])
	}

	t.Logf("=== EXPECTED STATES ===")
	for i, expected := range expectedStates {
		t.Logf("Expected %d: overallState=%s, componentSetState=%s, processState=%v, DB=%v, FS=%v",
			i, expected.OverallState, expected.ComponentSet.State, expected.ProcessState,
			expected.ComponentSet.Components["DB"], expected.ComponentSet.Components["FS"])
	}

	// Track if we've seen all expected states
	seenStates := make([]bool, len(expectedStates))
	var lastSeenIndex int

	// For each actual state change
	for traceIdx, change := range stateChanges {
		vars := change.Vars
		overallState := vars["overallState"].(string)
		componentSetState := vars["componentSetState"].(string)
		processState := vars["processState"].(string)
		dbState := vars["dbState"].(string)
		fsState := vars["fsState"].(string)

		t.Logf("=== COMPARING TRACE %d ===", traceIdx)
		t.Logf("Actual: overallState=%s, componentSetState=%s, processState=%s, dbState=%s, fsState=%s",
			overallState, componentSetState, processState, dbState, fsState)

		// Check if this state matches any expected state
		matched := false
		for i := lastSeenIndex; i < len(expectedStates); i++ {
			t.Logf("  Checking against expected state %d...", i)
			if matchesExpectedState(overallState, componentSetState, processState, dbState, fsState, expectedStates[i]) {
				t.Logf("  ✅ MATCHED expected state %d", i)
				seenStates[i] = true
				lastSeenIndex = i
				matched = true
				break
			} else {
				t.Logf("  ❌ No match with expected state %d", i)
			}
		}

		if !matched {
			// Print detailed state comparison before failing
			t.Errorf("\nSTATE MISMATCH at trace index %d (expected state index %d):", traceIdx, lastSeenIndex)
			if lastSeenIndex < len(expectedStates) {
				t.Errorf("  Expected: %+v", expectedStates[lastSeenIndex])
			} else {
				t.Errorf("  No more expected states (reached end of expected states list)")
			}
			t.Errorf("  Actual:   overallState=%s, componentSetState=%s, processState=%s, dbState=%s, fsState=%s",
				overallState, componentSetState, processState, dbState, fsState)
			t.FailNow()
		}
	}

	// Check if we saw all expected states
	var missingStates []int
	for i, seen := range seenStates {
		if !seen {
			missingStates = append(missingStates, i)
		}
	}

	if len(missingStates) > 0 {
		// Print detailed state comparison before failing
		t.Errorf("Did not see all expected states. Saw %d of %d states", len(stateChanges), len(expectedStates))
		t.Errorf("Missing states:")
		for _, i := range missingStates {
			t.Errorf("  State %d: %+v", i, expectedStates[i])
		}
		t.FailNow()
	}

	t.Logf("Verified %d state changes against %d expected states", len(stateChanges), len(expectedStates))
}
