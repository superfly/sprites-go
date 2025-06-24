package wsexec_test

import (
	"bytes"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
	"time"

	"github.com/sprite-env/packages/wsexec"
)

// TestLargeDataTransfer tests transferring large amounts of data
func TestLargeDataTransfer(t *testing.T) {
	// Create test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := &wsexec.ServerCommand{
			Path: "cat",
			Args: []string{"cat"},
		}

		if err := cmd.Handle(w, r); err != nil {
			t.Errorf("Server handle error: %v", err)
		}
	}))
	defer server.Close()

	// Create client
	req, err := http.NewRequest("GET", server.URL+"/exec/test/websocket", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}
	req.URL.Scheme = "ws"

	// Create large input data (1MB)
	largeData := strings.Repeat("A", 1024*1024)
	stdin := strings.NewReader(largeData)
	var stdout bytes.Buffer

	cmd := wsexec.Command(req, "cat")
	cmd.Stdin = stdin
	cmd.Stdout = &stdout

	start := time.Now()
	if err := cmd.Run(); err != nil {
		t.Fatalf("Command failed: %v", err)
	}
	duration := time.Since(start)

	// Check output
	if stdout.String() != largeData {
		t.Errorf("Data transfer failed: expected %d bytes, got %d bytes", len(largeData), stdout.Len())
	}

	t.Logf("Transferred %d bytes in %v", len(largeData), duration)
}

// TestBinaryDataIntegrity tests binary data transfer
func TestBinaryDataIntegrity(t *testing.T) {
	// Create test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := &wsexec.ServerCommand{
			Path: "cat",
			Args: []string{"cat"},
		}

		if err := cmd.Handle(w, r); err != nil {
			t.Errorf("Server handle error: %v", err)
		}
	}))
	defer server.Close()

	// Create client
	req, err := http.NewRequest("GET", server.URL+"/exec/test/websocket", nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}
	req.URL.Scheme = "ws"

	// Create binary data with all byte values
	binaryData := make([]byte, 256)
	for i := 0; i < 256; i++ {
		binaryData[i] = byte(i)
	}

	stdin := bytes.NewReader(binaryData)
	var stdout bytes.Buffer

	cmd := wsexec.Command(req, "cat")
	cmd.Stdin = stdin
	cmd.Stdout = &stdout

	if err := cmd.Run(); err != nil {
		t.Fatalf("Command failed: %v", err)
	}

	// Check binary integrity
	if !bytes.Equal(stdout.Bytes(), binaryData) {
		t.Error("Binary data integrity failed")
		for i, b := range stdout.Bytes() {
			if i < len(binaryData) && b != binaryData[i] {
				t.Errorf("Byte mismatch at index %d: expected %d, got %d", i, binaryData[i], b)
				break
			}
		}
	}
}

// BenchmarkSmallCommands benchmarks execution of small, quick commands
func BenchmarkSmallCommands(b *testing.B) {
	// Create test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := &wsexec.ServerCommand{
			Path: "echo",
			Args: []string{"echo", "benchmark"},
		}

		if err := cmd.Handle(w, r); err != nil {
			b.Errorf("Server handle error: %v", err)
		}
	}))
	defer server.Close()

	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		// Create client
		req, err := http.NewRequest("GET", server.URL+"/exec/test/websocket", nil)
		if err != nil {
			b.Fatalf("Failed to create request: %v", err)
		}
		req.URL.Scheme = "ws"

		var stdout bytes.Buffer
		cmd := wsexec.Command(req, "echo", "benchmark")
		cmd.Stdout = &stdout

		if err := cmd.Run(); err != nil {
			b.Fatalf("Command failed: %v", err)
		}
	}
}

// BenchmarkLargeDataTransfer benchmarks large data transfer
func BenchmarkLargeDataTransfer(b *testing.B) {
	// Create test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cmd := &wsexec.ServerCommand{
			Path: "cat",
			Args: []string{"cat"},
		}

		if err := cmd.Handle(w, r); err != nil {
			b.Errorf("Server handle error: %v", err)
		}
	}))
	defer server.Close()

	// Create test data (100KB)
	testData := strings.Repeat("X", 100*1024)

	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		// Create client
		req, err := http.NewRequest("GET", server.URL+"/exec/test/websocket", nil)
		if err != nil {
			b.Fatalf("Failed to create request: %v", err)
		}
		req.URL.Scheme = "ws"

		stdin := strings.NewReader(testData)
		var stdout bytes.Buffer

		cmd := wsexec.Command(req, "cat")
		cmd.Stdin = stdin
		cmd.Stdout = &stdout

		if err := cmd.Run(); err != nil {
			b.Fatalf("Command failed: %v", err)
		}

		if stdout.Len() != len(testData) {
			b.Fatalf("Expected %d bytes, got %d", len(testData), stdout.Len())
		}
	}
}
