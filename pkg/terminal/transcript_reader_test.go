package terminal

import (
	"context"
	"io"
	"os"
	"os/exec"
	"strings"
	"testing"
	"time"
)

func TestFileTranscriptReader(t *testing.T) {
	// Create a test transcript file
	testFile := "/tmp/test-transcript-reader.log"
	defer os.Remove(testFile)

	// Create FileTranscript and write some test data
	fileTranscript, err := NewFileTranscript(testFile)
	if err != nil {
		t.Fatalf("failed to create file transcript: %v", err)
	}

	stdoutWriter := fileTranscript.StreamWriter("stdout")
	stderrWriter := fileTranscript.StreamWriter("stderr")

	stdoutWriter.Write([]byte("stdout line 1\n"))
	stdoutWriter.Write([]byte("stdout line 2\n"))
	stderrWriter.Write([]byte("stderr line 1\n"))

	fileTranscript.Close()

	// Find the actual created file (has timestamp suffix)
	files, err := os.ReadDir("/tmp")
	if err != nil {
		t.Fatalf("failed to read temp directory: %v", err)
	}

	var actualFile string
	for _, file := range files {
		if strings.HasPrefix(file.Name(), "test-transcript-reader-") && strings.HasSuffix(file.Name(), ".log") {
			actualFile = "/tmp/" + file.Name()
			break
		}
	}

	if actualFile == "" {
		t.Fatal("transcript file not found")
	}
	defer os.Remove(actualFile)

	// Test reading the transcript
	reader, err := OpenTranscript(actualFile)
	if err != nil {
		t.Fatalf("failed to open transcript: %v", err)
	}
	defer reader.Close()

	ctx := context.Background()
	var lines []string

	for {
		line, err := reader.NextLine(ctx)
		if err == io.EOF {
			break
		}
		if err != nil {
			t.Fatalf("unexpected error reading line: %v", err)
		}
		lines = append(lines, line)
	}

	// Should have read all lines
	expected := []string{"stdout line 1", "stdout line 2", "stderr line 1"}
	if len(lines) != len(expected) {
		t.Errorf("expected %d lines, got %d", len(expected), len(lines))
	}

	for i, expectedLine := range expected {
		if i >= len(lines) {
			break
		}
		if !strings.Contains(lines[i], expectedLine) {
			t.Errorf("line %d: expected to contain %q, got %q", i, expectedLine, lines[i])
		}
	}
}

func TestFileTranscriptReaderWithStreamFilter(t *testing.T) {
	// Create a test transcript file with mixed streams
	testFile := "/tmp/test-transcript-filter.log"
	defer os.Remove(testFile)

	fileTranscript, err := NewFileTranscript(testFile)
	if err != nil {
		t.Fatalf("failed to create file transcript: %v", err)
	}

	stdoutWriter := fileTranscript.StreamWriter("stdout")
	stderrWriter := fileTranscript.StreamWriter("stderr")

	stdoutWriter.Write([]byte("stdout line\n"))
	stderrWriter.Write([]byte("stderr line\n"))

	fileTranscript.Close()

	// Find the actual file
	files, err := os.ReadDir("/tmp")
	if err != nil {
		t.Fatalf("failed to read temp directory: %v", err)
	}

	var actualFile string
	for _, file := range files {
		if strings.HasPrefix(file.Name(), "test-transcript-filter-") && strings.HasSuffix(file.Name(), ".log") {
			actualFile = "/tmp/" + file.Name()
			break
		}
	}
	defer os.Remove(actualFile)

	// Test stdout-only filter
	config := TranscriptReaderConfig{
		BufferSize:    100,
		FlushInterval: time.Second,
		Stream:        "stdout",
	}

	reader, err := OpenTranscriptWithConfig(actualFile, config)
	if err != nil {
		t.Fatalf("failed to open transcript: %v", err)
	}
	defer reader.Close()

	ctx := context.Background()
	var lines []string

	for {
		line, err := reader.NextLine(ctx)
		if err == io.EOF {
			break
		}
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}
		lines = append(lines, line)
	}

	// Should only have stdout lines
	if len(lines) != 1 {
		t.Errorf("expected 1 line, got %d", len(lines))
	}
	if len(lines) > 0 && !strings.Contains(lines[0], "stdout line") {
		t.Errorf("expected stdout line, got %q", lines[0])
	}
}

func TestLiveTranscriptReader(t *testing.T) {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	// Create a command that outputs multiple lines
	cmd := exec.Command("sh", "-c", "echo 'line 1'; echo 'line 2'; echo 'line 3'")
	reader, err := StreamTranscript(ctx, cmd)
	if err != nil {
		t.Fatalf("failed to create stream transcript: %v", err)
	}
	defer reader.Close()

	var lines []string
	for {
		line, err := reader.NextLine(ctx)
		if err == io.EOF {
			break
		}
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}
		lines = append(lines, line)
	}

	expected := []string{"line 1", "line 2", "line 3"}
	if len(lines) != len(expected) {
		t.Errorf("expected %d lines, got %d", len(expected), len(lines))
	}

	for i, expectedLine := range expected {
		if i >= len(lines) {
			break
		}
		if lines[i] != expectedLine {
			t.Errorf("line %d: expected %q, got %q", i, expectedLine, lines[i])
		}
	}
}

func TestLiveTranscriptReaderWithStderr(t *testing.T) {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	// Create command that outputs to both stdout and stderr
	cmd := exec.Command("sh", "-c", "echo 'stdout message'; echo 'stderr message' >&2")

	// Configure to read stderr only
	config := TranscriptReaderConfig{
		BufferSize:    100,
		FlushInterval: time.Second,
		Stream:        "stderr",
	}

	reader, err := StreamTranscriptWithConfig(ctx, cmd, config)
	if err != nil {
		t.Fatalf("failed to create stream transcript: %v", err)
	}
	defer reader.Close()

	var lines []string
	for {
		line, err := reader.NextLine(ctx)
		if err == io.EOF {
			break
		}
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}
		lines = append(lines, line)
	}

	// Should only have stderr output
	if len(lines) != 1 {
		t.Errorf("expected 1 line, got %d", len(lines))
	}
	if len(lines) > 0 && lines[0] != "stderr message" {
		t.Errorf("expected 'stderr message', got %q", lines[0])
	}
}

func TestMemoryTranscriptReader(t *testing.T) {
	ctx, cancel := context.WithTimeout(context.Background(), 3*time.Second)
	defer cancel()

	// Create a memory transcript and add some initial data
	transcript := NewMemoryTranscript()
	stdoutWriter := transcript.StreamWriter("stdout")

	stdoutWriter.Write([]byte("initial line 1\n"))
	stdoutWriter.Write([]byte("initial line 2\n"))

	// Create reader with faster flush interval for testing
	config := TranscriptReaderConfig{
		BufferSize:    100,
		FlushInterval: 100 * time.Millisecond,
		Stream:        "stdout",
	}

	reader := StreamMemoryTranscriptWithConfig(ctx, transcript, config)
	defer reader.Close()

	// Read initial lines
	line1, err := reader.NextLine(ctx)
	if err != nil {
		t.Fatalf("failed to read line 1: %v", err)
	}
	if line1 != "initial line 1" {
		t.Errorf("expected 'initial line 1', got %q", line1)
	}

	line2, err := reader.NextLine(ctx)
	if err != nil {
		t.Fatalf("failed to read line 2: %v", err)
	}
	if line2 != "initial line 2" {
		t.Errorf("expected 'initial line 2', got %q", line2)
	}

	// Add more data while reader is active
	stdoutWriter.Write([]byte("new line 1\n"))

	// Wait for flush interval and read new line
	time.Sleep(200 * time.Millisecond)

	line3, err := reader.NextLine(ctx)
	if err != nil {
		t.Fatalf("failed to read line 3: %v", err)
	}
	if line3 != "new line 1" {
		t.Errorf("expected 'new line 1', got %q", line3)
	}
}

func TestTranscriptReaderContextCancellation(t *testing.T) {
	ctx, cancel := context.WithCancel(context.Background())

	// Create a long-running command
	cmd := exec.Command("sleep", "10")
	reader, err := StreamTranscript(ctx, cmd)
	if err != nil {
		t.Fatalf("failed to create stream transcript: %v", err)
	}
	defer reader.Close()

	// Cancel the context after a short time
	go func() {
		time.Sleep(100 * time.Millisecond)
		cancel()
	}()

	// Try to read - should return context error
	_, err = reader.NextLine(ctx)
	if err == nil {
		t.Error("expected context cancellation error")
	}
	if err != context.Canceled {
		t.Errorf("expected context.Canceled, got %v", err)
	}
}

func TestTranscriptReaderClose(t *testing.T) {
	ctx := context.Background()

	// Test file reader close
	{
		// Create a temporary file for testing
		tmpFile := "/tmp/test-close.log"
		file, err := os.Create(tmpFile)
		if err != nil {
			t.Fatalf("failed to create temp file: %v", err)
		}
		file.WriteString("test line\n")
		file.Close()
		defer os.Remove(tmpFile)

		reader, err := OpenTranscript(tmpFile)
		if err != nil {
			t.Fatalf("failed to open transcript: %v", err)
		}

		// Close should not error
		if err := reader.Close(); err != nil {
			t.Errorf("close returned error: %v", err)
		}

		// Second close should not error
		if err := reader.Close(); err != nil {
			t.Errorf("second close returned error: %v", err)
		}
	}

	// Test live reader close
	{
		cmd := exec.Command("sleep", "1")
		reader, err := StreamTranscript(ctx, cmd)
		if err != nil {
			t.Fatalf("failed to create stream transcript: %v", err)
		}

		// Close should not error
		if err := reader.Close(); err != nil {
			t.Errorf("close returned error: %v", err)
		}

		// Reading after close should return EOF
		_, err = reader.NextLine(ctx)
		if err != io.EOF {
			t.Errorf("expected io.EOF after close, got %v", err)
		}
	}
}

func TestDefaultTranscriptReaderConfig(t *testing.T) {
	config := DefaultTranscriptReaderConfig()

	if config.BufferSize != 100 {
		t.Errorf("expected BufferSize 100, got %d", config.BufferSize)
	}
	if config.FlushInterval != time.Second {
		t.Errorf("expected FlushInterval 1s, got %v", config.FlushInterval)
	}
	if config.Stream != "all" {
		t.Errorf("expected Stream 'all', got %q", config.Stream)
	}
}
