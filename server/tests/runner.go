package tests

import (
	"bufio"
	"context"
	"encoding/json"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"testing"
	"time"
)

type StateChange struct {
	Vars map[string]interface{} `json:"vars"`
}

// killExistingSpriteEnvProcesses finds and kills any existing sprite-env processes
// This is equivalent to: ps aux | grep sprite-env | grep -v grep | awk '{print $2}' | xargs kill -9
func killExistingSpriteEnvProcesses(t *testing.T) {
	// Run ps aux to get all processes
	cmd := exec.Command("ps", "aux")
	output, err := cmd.Output()
	if err != nil {
		t.Logf("Warning: Failed to run ps aux: %v", err)
		return
	}

	// Parse the output line by line
	scanner := bufio.NewScanner(strings.NewReader(string(output)))
	var killedPids []int

	for scanner.Scan() {
		line := scanner.Text()

		// Skip if line doesn't contain sprite-env
		if !strings.Contains(line, "sprite-env") {
			continue
		}

		// Skip if line contains grep (avoid killing the grep process itself)
		if strings.Contains(line, "grep") {
			continue
		}

		// Parse the PID from the ps output (second column)
		fields := strings.Fields(line)
		if len(fields) < 2 {
			continue
		}

		pidStr := fields[1]
		pid, err := strconv.Atoi(pidStr)
		if err != nil {
			continue
		}

		// Skip our own process
		if pid == os.Getpid() {
			continue
		}

		// Try to kill the process
		process, err := os.FindProcess(pid)
		if err != nil {
			continue
		}

		// Send SIGKILL to the process
		err = process.Signal(syscall.SIGKILL)
		if err != nil {
			// Process might already be gone, which is fine
			continue
		}

		killedPids = append(killedPids, pid)
		t.Logf("Killed existing sprite-env process with PID %d", pid)
	}

	if len(killedPids) > 0 {
		// Give killed processes a moment to clean up
		time.Sleep(100 * time.Millisecond)
		t.Logf("Cleaned up %d existing sprite-env processes", len(killedPids))
	}
}

func RunTests(t *testing.T) {
	// Clean up any existing sprite-env processes first
	killExistingSpriteEnvProcesses(t)

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
	runTestWithExitCondition(t, dir, "ProcessStateMachine:Running")
}

func runTestWithExitCondition(t *testing.T, dir string, exitCondition string) {
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
	if _, err := os.Stat(supervisedProcessPath); os.IsNotExist(err) {
		t.Fatalf("Supervised process script not found: %s", supervisedProcessPath)
	}

	// Create command to run the server with absolute paths
	cmd := exec.Command(spriteEnvPath, "-tla-trace", "-test-dir", dir, "--", supervisedProcessPath)

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
		t.Fatalf("Failed to start command: %v", err)
	}

	// Start 10-second timeout - send SIGKILL if process is still running
	go func() {
		time.Sleep(10 * time.Second)
		fmt.Printf("TIMEOUT: sending SIGKILL\n")
		if err := cmd.Process.Kill(); err != nil {
			fmt.Printf("ERROR: failed to send SIGKILL: %v\n", err)
		}
	}()

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

	// Raw trace file
	traceFile, err := os.Create(filepath.Join("tmp", testName+"-raw.trace"))
	if err != nil {
		t.Fatalf("Failed to create trace file: %v", err)
	}
	defer traceFile.Close()

	// Initialize trace collection for valid JSON
	var traces []map[string]interface{}

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
					// Check for exit condition (skip if TIMEOUT)
					if exitCondition != "TIMEOUT" {
						if source, ok := vars["source"].(string); ok {
							if to, ok := vars["to"].(string); ok {
								currentTransition := fmt.Sprintf("%s:%s", source, to)
								if currentTransition == exitCondition {
									// Use stopOnce to ensure this only happens once
									stopOnce.Do(func() {
										if err := cmd.Process.Signal(os.Interrupt); err != nil {
											fmt.Printf("ERROR: failed to send SIGTERM: %v\n", err)
										}
										close(stopChan)
									})
								}
							}
						}
					}
					stateChanges <- StateChange{Vars: vars}
					// Collect trace for JSON output
					traces = append(traces, vars)
				}
			} else {
				// Print raw line if JSON parsing fails and line contains "{"
				if os.Getenv("TEST_VERBOSE") != "" && strings.Contains(line, "{") {
					t.Logf("FAILED JSON PARSE: %s", line)
				}
				// Forward stderr output only if verbose
				if os.Getenv("TEST_VERBOSE") != "" {
					os.Stderr.WriteString(line + "\n")
				}
			}
		}
		if err := scanner.Err(); err != nil {
			select {
			case <-ctx.Done():
				// Context cancelled - pipe closure is expected
				return
			default:
				// Process may have exited while we were reading - this is normal
				t.Logf("Error reading stderr: %v", err)
			}
		}
	}()

	// Start goroutine to forward stdout
	go func() {
		defer close(stdoutDone)
		scanner := bufio.NewScanner(stdout)
		for scanner.Scan() {
			select {
			case <-ctx.Done():
				return
			default:
				// Forward stdout to test output only if verbose
				line := scanner.Text()
				if os.Getenv("TEST_VERBOSE") != "" {
					t.Logf("STDOUT: %s", line)
				}
			}
		}
		if err := scanner.Err(); err != nil {
			select {
			case <-ctx.Done():
				// Context cancelled - pipe closure is expected
				return
			default:
				// Process may have exited while we were reading - this is normal
				t.Logf("Error reading stdout: %v", err)
			}
		}
	}()

	// Wait for completion signal (unless using TIMEOUT mode)
	if exitCondition != "TIMEOUT" {
		<-stopChan
	}

	// Wait for process to exit with timeout
	done := make(chan error, 1)
	go func() {
		done <- cmd.Wait()
	}()

	select {
	case err := <-done:
		// Process exited within timeout
		if err != nil {
			// Check if it's an exit error with a signal-based exit code
			if exitError, ok := err.(*exec.ExitError); ok {
				exitCode := exitError.ExitCode()
				// Accept signal-based exit codes (128 + signal number)
				// SIGINT = 130 (128 + 2), SIGTERM = 143 (128 + 15), SIGKILL = 137 (128 + 9)
				if exitCode != 130 && exitCode != 143 && exitCode != 137 {
					t.Fatalf("Process exited with unexpected exit code %d: %v", exitCode, err)
				}
			} else {
				t.Fatalf("Process exited with error: %v", err)
			}
		}
	case <-time.After(10 * time.Second):
		// Timeout - force kill the process
		fmt.Printf("TIMEOUT: sending SIGKILL\n")
		if err := cmd.Process.Kill(); err != nil {
			t.Fatalf("Failed to send SIGKILL: %v", err)
		}
		// Wait for the kill to take effect
		<-done
	}

	// Wait specifically for stderr and stdout goroutines to finish
	select {
	case <-stderrDone:
	case <-time.After(1 * time.Second):
	}

	select {
	case <-stdoutDone:
	case <-time.After(1 * time.Second):
	}

	// Collect state changes for analysis
	var collectedChanges []StateChange
	for change := range stateChanges {
		collectedChanges = append(collectedChanges, change)
	}

	// Write the complete traces as valid JSON
	if traceData, err := json.MarshalIndent(traces, "", "  "); err != nil {
		t.Errorf("Failed to marshal traces JSON: %v", err)
	} else {
		if _, err := traceFile.Write(traceData); err != nil {
			t.Errorf("Failed to write traces JSON: %v", err)
		}
	}

	// Verify we collected traces and log summary
	if len(collectedChanges) == 0 {
		t.Errorf("No TLA traces were collected - system may not be emitting traces properly")
	}

	// Build state transition summary
	var stateTransitions []string
	for _, change := range collectedChanges {
		if source, ok := change.Vars["source"].(string); ok {
			if from, ok := change.Vars["from"].(string); ok {
				if to, ok := change.Vars["to"].(string); ok {
					stateTransitions = append(stateTransitions, fmt.Sprintf("%s:%s→%s", source, from, to))
				}
			}
		}
	}

	fmt.Printf("%d traces → %s\n", len(collectedChanges), strings.Join(stateTransitions, " → "))
}

// ComponentConfig defines the scripts for a component
type ComponentConfig struct {
	Start      string // Script name in _shared
	Ready      string // Script name in _shared
	Checkpoint string // Script name in _shared (optional)
	Restore    string // Script name in _shared (optional)
}

// TestScenario defines a complete test scenario
type TestScenario struct {
	Name       string          // Test name
	DB         ComponentConfig // DB component configuration
	FS         ComponentConfig // FS component configuration
	Supervised string          // Supervised process script name
}

// Component configuration helpers
var (
	HealthyComponent = ComponentConfig{
		Start: "healthy_start.sh",
		Ready: "healthy_ready.sh",
	}

	CrashingComponent = ComponentConfig{
		Start: "crash_after_5s.sh",
		Ready: "healthy_ready.sh",
	}

	ReadyFailsComponent = ComponentConfig{
		Start: "healthy_start.sh",
		Ready: "ready_fails.sh",
	}

	ReadyNeverSucceedsComponent = ComponentConfig{
		Start: "healthy_start.sh",
		Ready: "ready_never_succeeds.sh",
	}

	IgnoresSignalsComponent = ComponentConfig{
		Start: "ignore_signals.sh",
		Ready: "healthy_ready.sh",
	}
)

// createTestDirectory creates a test directory with db and fs components using symlinks to shared scripts
func createTestDirectory(t *testing.T, scenario TestScenario) string {
	// Create base test directory in tmp
	testDir := filepath.Join("tmp", "dynamic-"+scenario.Name)

	// Clean up any existing directory
	if err := os.RemoveAll(testDir); err != nil {
		t.Fatalf("Failed to clean existing test directory: %v", err)
	}

	// Create the directory structure
	if err := os.MkdirAll(filepath.Join(testDir, "db"), 0755); err != nil {
		t.Fatalf("Failed to create db directory: %v", err)
	}
	if err := os.MkdirAll(filepath.Join(testDir, "fs"), 0755); err != nil {
		t.Fatalf("Failed to create fs directory: %v", err)
	}

	// Get absolute path to shared scripts
	sharedDir, err := filepath.Abs("../test-scripts/_shared")
	if err != nil {
		t.Fatalf("Failed to get shared directory path: %v", err)
	}

	// Helper function to create symlink for script
	createScript := func(componentDir, scriptType, scriptName string) {
		if scriptName == "" {
			return // Skip if no script specified
		}

		srcPath := filepath.Join(sharedDir, scriptName)
		destPath := filepath.Join(componentDir, scriptType+".sh")

		// Create symlink to shared script
		if err := os.Symlink(srcPath, destPath); err != nil {
			t.Fatalf("Failed to create symlink for %s: %v", destPath, err)
		}
	}

	// Create db component scripts
	dbDir := filepath.Join(testDir, "db")
	createScript(dbDir, "start", scenario.DB.Start)
	createScript(dbDir, "ready", scenario.DB.Ready)
	createScript(dbDir, "checkpoint", scenario.DB.Checkpoint)
	createScript(dbDir, "restore", scenario.DB.Restore)

	// Create fs component scripts
	fsDir := filepath.Join(testDir, "fs")
	createScript(fsDir, "start", scenario.FS.Start)
	createScript(fsDir, "ready", scenario.FS.Ready)
	createScript(fsDir, "checkpoint", scenario.FS.Checkpoint)
	createScript(fsDir, "restore", scenario.FS.Restore)

	// Create supervised process script
	supervisedPath := filepath.Join(testDir, "supervised-process.sh")
	srcSupervisedPath := filepath.Join(sharedDir, scenario.Supervised)
	if err := os.Symlink(srcSupervisedPath, supervisedPath); err != nil {
		t.Fatalf("Failed to create supervised process symlink: %v", err)
	}

	return testDir
}

// RunDynamicTests generates and runs several dynamic test scenarios using a test matrix
func RunDynamicTests(t *testing.T) {
	// Clean up any existing sprite-env processes first
	killExistingSpriteEnvProcesses(t)

	scenarios := []TestScenario{
		{
			Name:       "supervised-ignores-signals",
			DB:         HealthyComponent,
			FS:         HealthyComponent,
			Supervised: "ignore_signals.sh",
		},
		{
			Name:       "component-crashes-after-5s",
			DB:         CrashingComponent,
			FS:         HealthyComponent,
			Supervised: "run_forever.sh",
		},
		{
			Name:       "one-healthy-one-fails-ready",
			DB:         HealthyComponent,
			FS:         ReadyFailsComponent,
			Supervised: "run_forever.sh",
		},
		{
			Name:       "ready-never-succeeds",
			DB:         ReadyNeverSucceedsComponent,
			FS:         HealthyComponent,
			Supervised: "run_forever.sh",
		},
		{
			Name:       "component-ignores-signals",
			DB:         IgnoresSignalsComponent,
			FS:         HealthyComponent,
			Supervised: "run_forever.sh",
		},
	}

	// Run all scenarios with appropriate exit conditions
	for _, scenario := range scenarios {
		scenario := scenario // capture loop variable
		t.Run(scenario.Name, func(t *testing.T) {
			testDir := createTestDirectory(t, scenario)
			defer os.RemoveAll(testDir)

			// Choose exit condition based on test scenario
			var exitCondition string
			switch scenario.Name {
			case "supervised-ignores-signals", "component-ignores-signals":
				// Test shutdown behavior - exit when process is running
				exitCondition = "ProcessStateMachine:Running"
			case "component-crashes-after-5s":
				// Wait to see component crash - use timeout instead of immediate exit
				exitCondition = "TIMEOUT" // Special case: let it run until timeout
			case "one-healthy-one-fails-ready", "ready-never-succeeds":
				// Wait to see component failure behavior
				exitCondition = "ProcessStateMachine:Running" // For now, can be changed later
			default:
				exitCondition = "ProcessStateMachine:Running"
			}

			runTestWithExitCondition(t, testDir, exitCondition)
		})
	}
}
