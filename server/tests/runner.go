package tests

import (
	"bufio"
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
	ProcessState string            `json:"processState,omitempty"`
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

	// Create channels for state changes and completion
	stateChanges := make(chan StateChange, 100)
	stopChan := make(chan struct{})
	var stopOnce sync.Once
	var wg sync.WaitGroup
	wg.Add(2)

	// Start goroutine to scan stderr for state changes
	go func() {
		defer wg.Done()
		scanner := bufio.NewScanner(stderr)
		for scanner.Scan() {
			line := scanner.Text()
			// Try to parse the line as JSON
			var trace TraceOutput
			if err := json.Unmarshal([]byte(line), &trace); err == nil {
				t.Logf("Raw TLA trace: %s", line)
				if strings.Contains(line, "\"overallState\":\"Running\"") &&
					strings.Contains(line, "\"processState\":\"Running\"") &&
					!strings.Contains(line, "\"shutdownInProgress\":true") {
					t.Logf("Found initial Running state (string match), waiting 2 seconds before shutdown")
					time.Sleep(2 * time.Second)
					stopOnce.Do(func() { close(stopChan) })
				}
				t.Logf("Unmarshaled trace: %+v", trace)
				stateChanges <- StateChange{Vars: trace.Vars}
			} else {
				t.Logf("STDERR: %s", line)
			}
		}
		if err := scanner.Err(); err != nil {
			t.Fatalf("Error reading stderr: %v", err)
		}
	}()

	// Start goroutine to scan stdout for debug logs
	go func() {
		defer wg.Done()
		scanner := bufio.NewScanner(stdout)
		for scanner.Scan() {
			t.Logf("STDOUT: %s", scanner.Text())
		}
		if err := scanner.Err(); err != nil {
			t.Fatalf("Error reading stdout: %v", err)
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
		t.Fatalf("Process exited with error: %v", err)
	}

	// Close state changes channel and wait for goroutines
	close(stateChanges)
	wg.Wait()

	// Verify state changes against expected states
	verifyStateChanges(t, expectedStates.States, stateChanges)
}

func verifyStateChanges(t *testing.T, expectedStates []ExpectedState, actual chan StateChange) {
	currentStateIndex := 0
	stateChangesSeen := 0

	for stateChange := range actual {
		stateChangesSeen++
		if currentStateIndex >= len(expectedStates) {
			t.Fatalf("Unexpected state change after all expected states: %v", stateChange.Vars)
		}

		expected := expectedStates[currentStateIndex]

		// Safely extract state fields, failing if missing or nil
		overallState, ok := stateChange.Vars["overallState"].(string)
		if !ok {
			t.Fatalf("State change missing required field: overallState")
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
		shutdownInProgress, ok := stateChange.Vars["shutdownInProgress"].(bool)
		if !ok {
			t.Fatalf("State change missing required field: shutdownInProgress")
		}

		// Verify overall state
		if overallState != expected.OverallState {
			t.Errorf("Expected overall state %s, got %s", expected.OverallState, overallState)
		}

		// Verify component states
		if dbStates, ok := expected.ComponentSet.Components["DB"]; ok && len(dbStates) > 0 {
			if dbState != dbStates[0] {
				t.Errorf("Expected DB state %s, got %s", dbStates[0], dbState)
			}
		} else {
			t.Errorf("Expected DB state not found in expected states")
		}
		if fsStates, ok := expected.ComponentSet.Components["FS"]; ok && len(fsStates) > 0 {
			if fsState != fsStates[0] {
				t.Errorf("Expected FS state %s, got %s", fsStates[0], fsState)
			}
		} else {
			t.Errorf("Expected FS state not found in expected states")
		}
		if processState != expected.ProcessState {
			t.Errorf("Expected process state %s, got %s", expected.ProcessState, processState)
		}
		expectedShutdown := false
		if shutdown, ok := expected.ComponentSet.Components["shutdown"]; ok && len(shutdown) > 0 {
			expectedShutdown = shutdown[0] == "true"
		}
		if shutdownInProgress != expectedShutdown {
			t.Errorf("Expected shutdownInProgress %v, got %v", expectedShutdown, shutdownInProgress)
		}

		currentStateIndex++
	}

	if currentStateIndex < len(expectedStates) {
		t.Fatalf("Did not see all expected states. Saw %d of %d states", currentStateIndex, len(expectedStates))
	}

	t.Logf("Verified %d state changes against %d expected states", stateChangesSeen, len(expectedStates))
}
