package main

import (
	"fmt"
	"sync"
	"testing"
	"time"
)

func TestConcurrentCommands(t *testing.T) {
	spriteName := sharedSpriteName
	baseURL := getBaseURL()
	testCliPath := getTestCliPath(t)

	const numCommands = 10
	var wg sync.WaitGroup
	results := make(chan string, numCommands)
	errors := make(chan error, numCommands)

	// Launch concurrent commands
	for i := 0; i < numCommands; i++ {
		wg.Add(1)
		go func(id int) {
			defer wg.Done()

			output, err := runTestCli(testCliPath, baseURL, spriteName, 30*time.Second,
				"-base-url", baseURL, "-sprite", spriteName, "-output", "stdout", "echo", fmt.Sprintf("concurrent-command-%d", id))
			if err != nil {
				errors <- fmt.Errorf("concurrent command %d failed: %v", id, err)
				return
			}
			results <- output
		}(i)
	}

	// Wait for all commands to complete
	wg.Wait()
	close(results)
	close(errors)

	// Collect all errors
	var errs []error
	for err := range errors {
		if err != nil {
			errs = append(errs, err)
		}
	}

	// Check if any errors occurred
	if len(errs) > 0 {
		t.Fatalf("Concurrent commands test failed with %d errors: first error: %v", len(errs), errs[0])
	}

	// Collect and verify results
	seen := make(map[string]bool)
	for result := range results {
		seen[result] = true
	}

	// Verify we got all expected results
	for i := 0; i < numCommands; i++ {
		expected := fmt.Sprintf("concurrent-command-%d\n", i)
		if !seen[expected] {
			t.Fatalf("Concurrent commands test failed: missing result %q (got %d results)", expected, len(seen))
		}
	}
}
