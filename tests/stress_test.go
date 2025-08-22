package tests

import (
	"fmt"
	"math/rand"
	"os"
	"os/exec"
	"sort"
	"strings"
	"sync"
	"testing"
	"time"
)

// StressTestResult represents the result of a stress test session
type StressTestResult struct {
	SessionID    int
	Success      bool
	HangDetected bool
	EchoTimes    []time.Duration

	AverageEchoTime time.Duration
	MinEchoTime     time.Duration
	MaxEchoTime     time.Duration
	MedianEchoTime  time.Duration
	P95EchoTime     time.Duration
	P99EchoTime     time.Duration
	Error           string
}

// SessionStats represents statistics for a single session
type SessionStats struct {
	SessionID       int
	TotalCommands   int
	AverageEchoTime time.Duration
	MinEchoTime     time.Duration
	MaxEchoTime     time.Duration
	MedianEchoTime  time.Duration
	P95EchoTime     time.Duration
	P99EchoTime     time.Duration
}

// OverallStats represents overall statistics across all sessions
type OverallStats struct {
	TotalCommands   int
	AverageEchoTime time.Duration
	MinEchoTime     time.Duration
	MaxEchoTime     time.Duration
	MedianEchoTime  time.Duration
	P95EchoTime     time.Duration
	P99EchoTime     time.Duration
}

func TestStressConcurrentTTY(t *testing.T) {
	if os.Getenv("STRESS_TEST") != "1" {
		t.Skip("Stress test skipped (set STRESS_TEST=1 to run)")
	}

	containerID, cleanup := setupTestContainer(t)
	defer cleanup()

	// Wait for server to be ready
	waitForServer(t, containerID)

	token := getAPIToken(t, containerID)

	const numSessions = 20
	const testDuration = 30 * time.Second
	const echoTimeout = 2 * time.Second

	t.Logf("Starting stress test with %d concurrent TTY sessions for %v", numSessions, testDuration)

	var wg sync.WaitGroup
	results := make(chan StressTestResult, numSessions)
	stopTest := make(chan struct{})

	// Start all concurrent sessions with jitter
	for i := 0; i < numSessions; i++ {
		wg.Add(1)
		go func(sessionID int) {
			defer wg.Done()
			// Add random jitter to stagger session starts
			jitter := time.Duration(rand.Intn(1000)) * time.Millisecond
			time.Sleep(jitter)
			runStressSession(t, sessionID, containerID, token, testDuration, echoTimeout, results, stopTest)
		}(i)
	}

	// Wait for all sessions to complete or timeout
	done := make(chan struct{})
	go func() {
		wg.Wait()
		close(done)
	}()

	select {
	case <-done:
		t.Logf("All stress test sessions completed")
	case <-time.After(testDuration + 10*time.Second):
		t.Logf("Stress test timed out, stopping all sessions")
		close(stopTest)
		<-done
	}

	// Collect results and calculate statistics
	close(results)
	var totalSessions, successfulSessions, failedSessions, hangDetected int
	var allEchoTimes []time.Duration
	var sessionStats []SessionStats
	var failedResults []StressTestResult

	for result := range results {
		totalSessions++
		if result.Success {
			successfulSessions++
			allEchoTimes = append(allEchoTimes, result.EchoTimes...)
			sessionStats = append(sessionStats, SessionStats{
				SessionID:       result.SessionID,
				TotalCommands:   len(result.EchoTimes),
				AverageEchoTime: result.AverageEchoTime,
				MinEchoTime:     result.MinEchoTime,
				MaxEchoTime:     result.MaxEchoTime,
				MedianEchoTime:  result.MedianEchoTime,
				P95EchoTime:     result.P95EchoTime,
				P99EchoTime:     result.P99EchoTime,
			})
		} else {
			failedSessions++
			failedResults = append(failedResults, result)
			if result.HangDetected {
				hangDetected++
			}
		}
	}

	// Calculate overall statistics
	var overallStats OverallStats
	if len(allEchoTimes) > 0 {
		sort.Slice(allEchoTimes, func(i, j int) bool {
			return allEchoTimes[i] < allEchoTimes[j]
		})

		var total time.Duration
		for _, t := range allEchoTimes {
			total += t
		}

		overallStats = OverallStats{
			TotalCommands:   len(allEchoTimes),
			AverageEchoTime: total / time.Duration(len(allEchoTimes)),
			MinEchoTime:     allEchoTimes[0],
			MaxEchoTime:     allEchoTimes[len(allEchoTimes)-1],
			MedianEchoTime:  allEchoTimes[len(allEchoTimes)/2],
			P95EchoTime:     allEchoTimes[int(float64(len(allEchoTimes))*0.95)],
			P99EchoTime:     allEchoTimes[int(float64(len(allEchoTimes))*0.99)],
		}
	}

	// Report results
	t.Logf("Stress test results:")
	t.Logf("  Total sessions: %d", totalSessions)
	t.Logf("  Successful sessions: %d", successfulSessions)
	t.Logf("  Failed sessions: %d", failedSessions)
	t.Logf("  Hangs detected: %d", hangDetected)

	if overallStats.TotalCommands > 0 {
		t.Logf("Overall echo time statistics:")
		t.Logf("  Total commands: %d", overallStats.TotalCommands)
		t.Logf("  Average: %v", overallStats.AverageEchoTime)
		t.Logf("  Min: %v", overallStats.MinEchoTime)
		t.Logf("  Median: %v", overallStats.MedianEchoTime)
		t.Logf("  95th percentile: %v", overallStats.P95EchoTime)
		t.Logf("  99th percentile: %v", overallStats.P99EchoTime)
		t.Logf("  Max: %v", overallStats.MaxEchoTime)

	}

	// Print failed session statistics
	if failedSessions > 0 {
		t.Logf("Failed session statistics:")
		for _, result := range failedResults {
			t.Logf("  Session %d: %s", result.SessionID, result.Error)
		}
	}

	// Fail if too many sessions failed or hangs detected
	if failedSessions > numSessions/4 { // More than 25% failure rate
		t.Errorf("Too many failed sessions: %d/%d", failedSessions, totalSessions)
	}
	if hangDetected > 0 {
		t.Errorf("Detected %d hangs in stress test", hangDetected)
	}
}

func TestQuickStressTTY(t *testing.T) {
	if os.Getenv("QUICK_STRESS_TEST") != "1" {
		t.Skip("Quick stress test skipped (set QUICK_STRESS_TEST=1 to run)")
	}

	containerID, cleanup := setupTestContainer(t)
	defer cleanup()

	// Wait for server to be ready
	waitForServer(t, containerID)

	token := getAPIToken(t, containerID)

	const numSessions = 3
	const testDuration = 10 * time.Second
	const echoTimeout = 1 * time.Second

	t.Logf("Starting quick stress test with %d concurrent TTY sessions for %v", numSessions, testDuration)

	var wg sync.WaitGroup
	results := make(chan StressTestResult, numSessions)
	stopTest := make(chan struct{})

	// Start all concurrent sessions with jitter
	for i := 0; i < numSessions; i++ {
		wg.Add(1)
		go func(sessionID int) {
			defer wg.Done()
			// Add random jitter to stagger session starts
			jitter := time.Duration(rand.Intn(500)) * time.Millisecond
			time.Sleep(jitter)
			runStressSession(t, sessionID, containerID, token, testDuration, echoTimeout, results, stopTest)
		}(i)
	}

	// Wait for all sessions to complete or timeout
	done := make(chan struct{})
	go func() {
		wg.Wait()
		close(done)
	}()

	select {
	case <-done:
		t.Logf("All quick stress test sessions completed")
	case <-time.After(testDuration + 5*time.Second):
		t.Logf("Quick stress test timed out, stopping all sessions")
		close(stopTest)
		<-done
	}

	// Collect results and calculate statistics
	close(results)
	var totalSessions, successfulSessions, failedSessions, hangDetected int
	var allEchoTimes []time.Duration
	var sessionStats []SessionStats
	var failedResults []StressTestResult

	for result := range results {
		totalSessions++
		if result.Success {
			successfulSessions++
			allEchoTimes = append(allEchoTimes, result.EchoTimes...)
			sessionStats = append(sessionStats, SessionStats{
				SessionID:       result.SessionID,
				TotalCommands:   len(result.EchoTimes),
				AverageEchoTime: result.AverageEchoTime,
				MinEchoTime:     result.MinEchoTime,
				MaxEchoTime:     result.MaxEchoTime,
				MedianEchoTime:  result.MedianEchoTime,
				P95EchoTime:     result.P95EchoTime,
				P99EchoTime:     result.P99EchoTime,
			})
		} else {
			failedSessions++
			failedResults = append(failedResults, result)
			if result.HangDetected {
				hangDetected++
			}
		}
	}

	// Calculate overall statistics
	var overallStats OverallStats
	if len(allEchoTimes) > 0 {
		sort.Slice(allEchoTimes, func(i, j int) bool {
			return allEchoTimes[i] < allEchoTimes[j]
		})

		var total time.Duration
		for _, t := range allEchoTimes {
			total += t
		}

		overallStats = OverallStats{
			TotalCommands:   len(allEchoTimes),
			AverageEchoTime: total / time.Duration(len(allEchoTimes)),
			MinEchoTime:     allEchoTimes[0],
			MaxEchoTime:     allEchoTimes[len(allEchoTimes)-1],
			MedianEchoTime:  allEchoTimes[len(allEchoTimes)/2],
			P95EchoTime:     allEchoTimes[int(float64(len(allEchoTimes))*0.95)],
			P99EchoTime:     allEchoTimes[int(float64(len(allEchoTimes))*0.99)],
		}
	}

	// Report results
	t.Logf("Quick stress test results:")
	t.Logf("  Total sessions: %d", totalSessions)
	t.Logf("  Successful sessions: %d", successfulSessions)
	t.Logf("  Failed sessions: %d", failedSessions)
	t.Logf("  Hangs detected: %d", hangDetected)

	if overallStats.TotalCommands > 0 {
		t.Logf("Overall echo time statistics:")
		t.Logf("  Total commands: %d", overallStats.TotalCommands)
		t.Logf("  Average: %v", overallStats.AverageEchoTime)
		t.Logf("  Min: %v", overallStats.MinEchoTime)
		t.Logf("  Median: %v", overallStats.MedianEchoTime)
		t.Logf("  95th percentile: %v", overallStats.P95EchoTime)
		t.Logf("  99th percentile: %v", overallStats.P99EchoTime)
		t.Logf("  Max: %v", overallStats.MaxEchoTime)

	}

	// Print failed session statistics
	if failedSessions > 0 {
		t.Logf("Failed session statistics:")
		for _, result := range failedResults {
			t.Logf("  Session %d: %s", result.SessionID, result.Error)
		}
	}

	// Fail if any hangs detected
	if hangDetected > 0 {
		t.Errorf("Detected %d hangs in quick stress test", hangDetected)
	}
}

func runStressSession(t *testing.T, sessionID int, containerID, token string, testDuration, echoTimeout time.Duration, results chan<- StressTestResult, stopTest <-chan struct{}) {
	session := NewInteractiveTTYSession(t, containerID, token, []string{"/bin/sh"})
	defer session.Close()

	// Wait for initial prompt
	if err := session.WaitForOutput("#", 5*time.Second); err != nil {
		results <- StressTestResult{
			SessionID: sessionID,
			Success:   false,
			Error:     fmt.Sprintf("Failed to get initial prompt: %v", err),
		}
		return
	}

	var echoTimes []time.Duration
	startTime := time.Now()
	commandCount := 0

	// Run echo commands continuously until test duration expires
	for time.Since(startTime) < testDuration {
		select {
		case <-stopTest:
			break
		default:
		}

		commandCount++

		command := fmt.Sprintf("echo 'stress-test-%d-command-%d'\r\n", sessionID, commandCount)

		// Add jitter to command sending (0-200ms random delay)
		jitter := time.Duration(rand.Intn(200)) * time.Millisecond
		time.Sleep(jitter)

		echoStart := time.Now()
		if err := session.SendInput(command); err != nil {
			results <- StressTestResult{
				SessionID: sessionID,
				Success:   false,
				Error:     fmt.Sprintf("Failed to send command: %v", err),
			}
			return
		}

		// Wait for echo response
		expectedOutput := fmt.Sprintf("stress-test-%d-command-%d", sessionID, commandCount)
		if err := session.WaitForOutput(expectedOutput, echoTimeout); err != nil {
			results <- StressTestResult{
				SessionID:    sessionID,
				Success:      false,
				HangDetected: true,
				Error:        fmt.Sprintf("Echo timeout after %v: %v", echoTimeout, err),
			}
			return
		}

		echoTime := time.Since(echoStart)
		echoTimes = append(echoTimes, echoTime)

		// Fail if echo takes more than 10ms
		if echoTime > 10*time.Millisecond {
			results <- StressTestResult{
				SessionID:    sessionID,
				Success:      false,
				HangDetected: true,
				Error:        fmt.Sprintf("Echo too slow: %v (threshold: 10ms)", echoTime),
				EchoTimes:    echoTimes,
			}
			return
		}

		// Small delay between commands
		time.Sleep(100 * time.Millisecond)
	}

	// Calculate statistics
	var totalEchoTime time.Duration
	var minEchoTime, maxEchoTime time.Duration
	var medianEchoTime, p95EchoTime, p99EchoTime time.Duration

	if len(echoTimes) > 0 {
		// Sort echo times for statistics
		sortedTimes := make([]time.Duration, len(echoTimes))
		copy(sortedTimes, echoTimes)
		sort.Slice(sortedTimes, func(i, j int) bool {
			return sortedTimes[i] < sortedTimes[j]
		})

		// Calculate total and min/max
		totalEchoTime = sortedTimes[0] // Start with first value
		minEchoTime = sortedTimes[0]
		maxEchoTime = sortedTimes[len(sortedTimes)-1]

		for i := 1; i < len(sortedTimes); i++ {
			totalEchoTime += sortedTimes[i]
		}

		// Calculate median
		if len(sortedTimes)%2 == 0 {
			medianEchoTime = (sortedTimes[len(sortedTimes)/2-1] + sortedTimes[len(sortedTimes)/2]) / 2
		} else {
			medianEchoTime = sortedTimes[len(sortedTimes)/2]
		}

		// Calculate 95th and 99th percentiles
		if len(sortedTimes) > 0 {
			p95Index := int(float64(len(sortedTimes)) * 0.95)
			if p95Index < len(sortedTimes) {
				p95EchoTime = sortedTimes[p95Index]
			}

			p99Index := int(float64(len(sortedTimes)) * 0.99)
			if p99Index < len(sortedTimes) {
				p99EchoTime = sortedTimes[p99Index]
			}
		}
	}

	averageEchoTime := time.Duration(0)
	if len(echoTimes) > 0 {
		averageEchoTime = totalEchoTime / time.Duration(len(echoTimes))
	}

	results <- StressTestResult{
		SessionID:       sessionID,
		Success:         true,
		EchoTimes:       echoTimes,
		AverageEchoTime: averageEchoTime,
		MinEchoTime:     minEchoTime,
		MaxEchoTime:     maxEchoTime,
		MedianEchoTime:  medianEchoTime,
		P95EchoTime:     p95EchoTime,
		P99EchoTime:     p99EchoTime,
	}
}

// printContainerLogs prints WARN and ERROR level logs from Docker container
func printContainerLogs(t *testing.T, containerID string) {
	cmd := exec.Command("docker", "logs", "--tail", "100", containerID)
	output, err := cmd.CombinedOutput()
	if err != nil {
		t.Logf("Failed to get container logs: %v", err)
		return
	}

	// Split output into lines and filter for WARN/ERROR only
	lines := strings.Split(string(output), "\n")
	warnErrorCount := 0
	for _, line := range lines {
		if line != "" {
			// Check if line contains WARN or ERROR level logs (exclude INFO)
			if (strings.Contains(line, "level=WARN") || strings.Contains(line, "level=ERROR")) ||
				(strings.Contains(line, "WARN") || strings.Contains(line, "ERROR") ||
					strings.Contains(line, "error") || strings.Contains(line, "failed")) &&
					!strings.Contains(line, "level=INFO") {
				t.Logf("  %s", line)
				warnErrorCount++
			}
		}
	}

	if warnErrorCount == 0 {
		t.Logf("  No WARN/ERROR logs found")
	}
}
