// +build linux

package policy

import (
	"context"
	"fmt"
	"net"
	"sync"
	"testing"
	"time"

	"github.com/miekg/dns"
)

// TestDNSServerConcurrentQueries tests that concurrent DNS queries work correctly
// without ID mismatches, deadlocks, or race conditions
func TestDNSServerConcurrentQueries(t *testing.T) {
	if testing.Short() {
		t.Skip("skipping integration test in short mode")
	}

	ctx := context.Background()

	// Create DNS server with empty rules (unrestricted mode)
	server, err := NewDNSServer(ctx, []Rule{}, "test_table", "test_v4", "test_v6", "")
	if err != nil {
		t.Fatalf("failed to create DNS server: %v", err)
	}
	defer server.Shutdown(ctx)

	// Test concurrent queries
	const numQueries = 50
	var wg sync.WaitGroup
	errors := make(chan error, numQueries)
	durations := make(chan time.Duration, numQueries)

	// Launch concurrent DNS queries
	for i := 0; i < numQueries; i++ {
		wg.Add(1)
		go func(queryNum int) {
			defer wg.Done()

			start := time.Now()

			// Create DNS query
			m := new(dns.Msg)
			m.SetQuestion(fmt.Sprintf("test%d.example.com.", queryNum), dns.TypeA)
			m.Id = uint16(queryNum + 1000) // Unique ID per query

			// Create mock ResponseWriter
			mockWriter := &mockResponseWriter{
				expectedID: m.Id,
			}

			// Process the query
			server.ServeDNS(mockWriter, m)

			duration := time.Since(start)
			durations <- duration

			// Check for ID mismatch
			if mockWriter.response != nil && mockWriter.response.Id != m.Id {
				errors <- fmt.Errorf("query %d: ID mismatch: expected %d, got %d",
					queryNum, m.Id, mockWriter.response.Id)
			}
		}(i)
	}

	// Wait for all queries to complete
	done := make(chan struct{})
	go func() {
		wg.Wait()
		close(done)
	}()

	// Timeout after 30 seconds (should complete much faster)
	select {
	case <-done:
		// Success
	case <-time.After(30 * time.Second):
		t.Fatal("test timed out - possible deadlock")
	}

	close(errors)
	close(durations)

	// Check for errors
	for err := range errors {
		t.Error(err)
	}

	// Analyze performance
	var totalDuration time.Duration
	var maxDuration time.Duration
	count := 0
	for d := range durations {
		totalDuration += d
		if d > maxDuration {
			maxDuration = d
		}
		count++
	}

	if count > 0 {
		avgDuration := totalDuration / time.Duration(count)
		t.Logf("Completed %d concurrent DNS queries", count)
		t.Logf("Average duration: %v", avgDuration)
		t.Logf("Max duration: %v", maxDuration)

		// Warn if queries are too slow (should be fast in unrestricted mode)
		if avgDuration > 500*time.Millisecond {
			t.Logf("WARNING: Average query time is slow (%v) - may indicate performance issues", avgDuration)
		}
	}
}

// TestDNSServerIDPreservation tests that DNS transaction IDs are preserved correctly
func TestDNSServerIDPreservation(t *testing.T) {
	ctx := context.Background()

	server, err := NewDNSServer(ctx, []Rule{}, "test_table", "test_v4", "test_v6", "")
	if err != nil {
		t.Fatalf("failed to create DNS server: %v", err)
	}
	defer server.Shutdown(ctx)

	testCases := []struct {
		name       string
		queryID    uint16
		domainName string
	}{
		{"small ID", 1, "test1.example.com."},
		{"medium ID", 12345, "test2.example.com."},
		{"large ID", 65535, "test3.example.com."},
		{"zero ID", 0, "test4.example.com."},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			m := new(dns.Msg)
			m.SetQuestion(tc.domainName, dns.TypeA)
			m.Id = tc.queryID

			mockWriter := &mockResponseWriter{expectedID: tc.queryID}
			server.ServeDNS(mockWriter, m)

			if mockWriter.response == nil {
				t.Fatal("no response received")
			}

			if mockWriter.response.Id != tc.queryID {
				t.Errorf("ID mismatch: expected %d, got %d", tc.queryID, mockWriter.response.Id)
			}
		})
	}
}

// TestDNSServerRepeatedQueries tests that repeated queries work correctly without caching
func TestDNSServerRepeatedQueries(t *testing.T) {
	ctx := context.Background()

	server, err := NewDNSServer(ctx, []Rule{}, "test_table", "test_v4", "test_v6", "")
	if err != nil {
		t.Fatalf("failed to create DNS server: %v", err)
	}
	defer server.Shutdown(ctx)

	domain := "repeated.example.com."

	// First query
	m1 := new(dns.Msg)
	m1.SetQuestion(domain, dns.TypeA)
	m1.Id = 100

	mockWriter1 := &mockResponseWriter{expectedID: 100}
	server.ServeDNS(mockWriter1, m1)

	if mockWriter1.response == nil {
		t.Fatal("no response to first query")
	}
	if mockWriter1.response.Id != 100 {
		t.Errorf("first query ID mismatch: expected 100, got %d", mockWriter1.response.Id)
	}

	// Second query with different ID - should work without caching issues
	m2 := new(dns.Msg)
	m2.SetQuestion(domain, dns.TypeA)
	m2.Id = 200

	mockWriter2 := &mockResponseWriter{expectedID: 200}
	server.ServeDNS(mockWriter2, m2)

	if mockWriter2.response == nil {
		t.Fatal("no response to second query")
	}
	if mockWriter2.response.Id != 200 {
		t.Errorf("second query ID mismatch: expected 200, got %d", mockWriter2.response.Id)
	}

	t.Log("Both queries completed with correct IDs - no caching issues")
}

// TestDNSServerRuleEvaluationConcurrent tests concurrent rule evaluation for race conditions
func TestDNSServerRuleEvaluationConcurrent(t *testing.T) {
	ctx := context.Background()

	rules := []Rule{
		{Domain: "allowed.com", Action: "allow"},
		{Domain: "*.allowed.com", Action: "allow"},
		{Domain: "blocked.com", Action: "deny"},
	}

	server, err := NewDNSServer(ctx, rules, "test_table", "test_v4", "test_v6", "")
	if err != nil {
		t.Fatalf("failed to create DNS server: %v", err)
	}
	defer server.Shutdown(ctx)

	testDomains := []string{
		"allowed.com",
		"sub.allowed.com",
		"blocked.com",
		"unknown.com",
	}

	var wg sync.WaitGroup
	for i := 0; i < 100; i++ {
		wg.Add(1)
		go func(iteration int) {
			defer wg.Done()
			domain := testDomains[iteration%len(testDomains)]
			result := server.isAllowed(domain)
			_ = result // Just checking for race conditions, not result
		}(i)
	}

	done := make(chan struct{})
	go func() {
		wg.Wait()
		close(done)
	}()

	select {
	case <-done:
		// Success - no deadlock
	case <-time.After(5 * time.Second):
		t.Fatal("test timed out - possible deadlock in isAllowed()")
	}
}

// Mock ResponseWriter for testing
type mockResponseWriter struct {
	expectedID uint16
	response   *dns.Msg
	localAddr  net.Addr
	remoteAddr net.Addr
}

func (m *mockResponseWriter) LocalAddr() net.Addr {
	if m.localAddr != nil {
		return m.localAddr
	}
	return &net.UDPAddr{IP: net.ParseIP("127.0.0.1"), Port: 53}
}

func (m *mockResponseWriter) RemoteAddr() net.Addr {
	if m.remoteAddr != nil {
		return m.remoteAddr
	}
	return &net.UDPAddr{IP: net.ParseIP("127.0.0.1"), Port: 54321}
}

func (m *mockResponseWriter) WriteMsg(msg *dns.Msg) error {
	m.response = msg
	return nil
}

func (m *mockResponseWriter) Write(b []byte) (int, error) {
	return len(b), nil
}

func (m *mockResponseWriter) Close() error {
	return nil
}

func (m *mockResponseWriter) TsigStatus() error {
	return nil
}

func (m *mockResponseWriter) TsigTimersOnly(bool) {}

func (m *mockResponseWriter) Hijack() {}



