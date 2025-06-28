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

	// Verify session ID is set
	if reader.SessionID() == "" {
		t.Error("session ID should not be empty")
	}

	// Read at least one line
	line, err := reader.NextLine(ctx)
	if err != nil && err != io.EOF {
		t.Fatalf("failed to read line: %v", err)
	}

	if err != io.EOF {
		if line.Text != "test message" {
			t.Errorf("expected 'test message', got %q", line.Text)
		}
		if line.SessionID != reader.SessionID() {
			t.Errorf("line session ID should match reader session ID")
		}
		if line.Sequence <= 0 {
			t.Errorf("sequence should be positive, got %d", line.Sequence)
		}
		if line.Stream != "stdout" {
			t.Errorf("expected stream 'stdout', got %q", line.Stream)
		}
	}

	// Test 2: Memory transcript streaming
	memTranscript := NewMemoryTranscript()
	stdoutWriter := memTranscript.StreamWriter("stdout")
	stdoutWriter.Write([]byte("memory test\n"))

	sessionID := "test-session-" + time.Now().Format("20060102150405")
	memReader := StreamMemoryTranscript(ctx, sessionID, memTranscript)
	defer memReader.Close()

	if memReader.SessionID() != sessionID {
		t.Errorf("expected session ID %q, got %q", sessionID, memReader.SessionID())
	}

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
		file.WriteString(`time=2024-01-01T00:00:00Z level=INFO msg=io stream=stdout line="test file line"` + "\n")
		file.Close()

		fileReader, err := OpenTranscriptFile(tmpFile)
		if err != nil {
			t.Errorf("failed to open transcript: %v", err)
		} else {
			defer fileReader.Close()
			// Just verify we can call NextLine without panic
			line, err := fileReader.NextLine(ctx)
			if err != nil && err != io.EOF {
				t.Errorf("unexpected error reading file: %v", err)
			}
			if err == nil && line != nil {
				if line.Text != "test file line" {
					t.Errorf("expected 'test file line', got %q", line.Text)
				}
			}
		}
	}

	// Test 5: NextLineAfter functionality
	cmd2 := exec.Command("sh", "-c", "echo line1; echo line2; echo line3")
	reader2, err := StreamTranscript(ctx, cmd2)
	if err != nil {
		t.Fatalf("failed to create second stream transcript: %v", err)
	}
	defer reader2.Close()

	// Read first line
	firstLine, err := reader2.NextLine(ctx)
	if err != nil && err != io.EOF {
		t.Fatalf("failed to read first line: %v", err)
	}

	if err != io.EOF && firstLine != nil {
		// Try to get next line after the first
		nextLine, err := reader2.NextLineAfter(ctx, firstLine.Sequence)
		if err != nil && err != io.EOF {
			t.Errorf("failed to read line after sequence %d: %v", firstLine.Sequence, err)
		}
		if err != io.EOF && nextLine != nil && nextLine.Sequence <= firstLine.Sequence {
			t.Errorf("next line sequence %d should be > %d", nextLine.Sequence, firstLine.Sequence)
		}
	}
}
