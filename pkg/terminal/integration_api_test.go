package terminal

import (
	"context"
	"io"
	"os"
	"os/exec"
	"testing"
	"time"
)

// Simple integration test to verify the new API compiles and basic functionality works
func TestTranscriptReaderAPIIntegration(t *testing.T) {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	// Test 1: Live streaming with a simple command
	cmd := exec.Command("echo", "test message")
	reader, err := StreamTranscript(ctx, cmd)
	if err != nil {
		t.Fatalf("failed to create stream transcript: %v", err)
	}
	defer reader.Close()

	// Read at least one line
	line, err := reader.NextLine(ctx)
	if err != nil && err != io.EOF {
		t.Fatalf("failed to read line: %v", err)
	}

	if err != io.EOF && line != "test message" {
		t.Errorf("expected 'test message', got %q", line)
	}

	// Test 2: Memory transcript streaming
	memTranscript := NewMemoryTranscript()
	stdoutWriter := memTranscript.StreamWriter("stdout")
	stdoutWriter.Write([]byte("memory test\n"))

	memReader := StreamMemoryTranscript(ctx, memTranscript)
	defer memReader.Close()

	// Test 3: Configuration
	config := DefaultTranscriptReaderConfig()
	if config.BufferSize <= 0 {
		t.Error("buffer size should be positive")
	}
	if config.FlushInterval <= 0 {
		t.Error("flush interval should be positive")
	}
	if config.Stream == "" {
		t.Error("stream should not be empty")
	}

	// Test 4: File operations (if we can create a simple log file)
	tmpFile := "/tmp/api-test.log"
	defer os.Remove(tmpFile)

	// Create a simple log file
	file, err := os.Create(tmpFile)
	if err == nil {
		file.WriteString(`time=2024-01-01T00:00:00Z level=INFO msg=io stream=stdout line="test file line"`)
		file.Close()

		fileReader, err := OpenTranscript(tmpFile)
		if err != nil {
			t.Errorf("failed to open transcript: %v", err)
		} else {
			defer fileReader.Close()
			// Just verify we can call NextLine without panic
			_, _ = fileReader.NextLine(ctx)
		}
	}
}
