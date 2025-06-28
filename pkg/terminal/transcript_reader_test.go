package terminal

import (
	"context"
	"io"
	"os"
	"os/exec"
	"strings"
	"testing"
	"time"

	"github.com/google/uuid"
)

func TestFileTranscriptBackend(t *testing.T) {
	// Create a test transcript file
	testFile := "/tmp/test-transcript-backend.log"
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
		if strings.HasPrefix(file.Name(), "test-transcript-backend-") && strings.HasSuffix(file.Name(), ".log") {
			actualFile = "/tmp/" + file.Name()
			break
		}
	}

	if actualFile == "" {
		t.Fatal("transcript file not found")
	}
	defer os.Remove(actualFile)

	// Test the backend directly
	backend, err := NewFileTranscriptBackend(actualFile)
	if err != nil {
		t.Fatalf("failed to create backend: %v", err)
	}
	defer backend.Close()

	sessionID := uuid.New().String()
	query := LineQuery{
		SessionID:     sessionID,
		AfterSequence: 0,
		Stream:        "all",
		Limit:         10,
		Follow:        false,
	}

	lines, err := backend.GetLines(context.Background(), query)
	if err != nil {
		t.Fatalf("failed to get lines: %v", err)
	}

	// Should have parsed all lines
	expected := []string{"stdout line 1", "stdout line 2", "stderr line 1"}
	if len(lines) != len(expected) {
		t.Errorf("expected %d lines, got %d", len(expected), len(lines))
	}

	for i, expectedText := range expected {
		if i >= len(lines) {
			break
		}
		if lines[i].Text != expectedText {
			t.Errorf("line %d: expected %q, got %q", i, expectedText, lines[i].Text)
		}
		if lines[i].SessionID != sessionID {
			t.Errorf("line %d: expected session ID %q, got %q", i, sessionID, lines[i].SessionID)
		}
		if lines[i].Sequence != int64(i+1) {
			t.Errorf("line %d: expected sequence %d, got %d", i, i+1, lines[i].Sequence)
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

	reader, err := OpenTranscriptFileWithConfig(actualFile, config)
	if err != nil {
		t.Fatalf("failed to open transcript: %v", err)
	}
	defer reader.Close()

	ctx := context.Background()
	var lines []*TranscriptLine

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
	if len(lines) > 0 && lines[0].Text != "stdout line" {
		t.Errorf("expected 'stdout line', got %q", lines[0].Text)
	}
	if len(lines) > 0 && lines[0].Stream != "stdout" {
		t.Errorf("expected stream 'stdout', got %q", lines[0].Stream)
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

	// Verify session ID is set
	if reader.SessionID() == "" {
		t.Error("session ID should not be empty")
	}

	var lines []*TranscriptLine
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
		if lines[i].Text != expectedLine {
			t.Errorf("line %d: expected %q, got %q", i, expectedLine, lines[i].Text)
		}
		if lines[i].SessionID != reader.SessionID() {
			t.Errorf("line %d: session ID mismatch", i)
		}
		if lines[i].Sequence != int64(i+1) {
			t.Errorf("line %d: expected sequence %d, got %d", i, i+1, lines[i].Sequence)
		}
		if lines[i].Stream != "stdout" {
			t.Errorf("line %d: expected stream 'stdout', got %q", i, lines[i].Stream)
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

	var lines []*TranscriptLine
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
	if len(lines) > 0 && lines[0].Text != "stderr message" {
		t.Errorf("expected 'stderr message', got %q", lines[0].Text)
	}
	if len(lines) > 0 && lines[0].Stream != "stderr" {
		t.Errorf("expected stream 'stderr', got %q", lines[0].Stream)
	}
}

func TestMemoryTranscriptBackend(t *testing.T) {
	ctx, cancel := context.WithTimeout(context.Background(), 3*time.Second)
	defer cancel()

	// Create a memory transcript and add some initial data
	transcript := NewMemoryTranscript()
	stdoutWriter := transcript.StreamWriter("stdout")

	stdoutWriter.Write([]byte("initial line 1\n"))
	stdoutWriter.Write([]byte("initial line 2\n"))

	// Test the backend directly
	sessionID := uuid.New().String()
	backend := NewMemoryTranscriptBackend(sessionID, transcript)
	defer backend.Close()

	query := LineQuery{
		SessionID:     sessionID,
		AfterSequence: 0,
		Stream:        "stdout",
		Limit:         10,
		Follow:        false,
	}

	lines, err := backend.GetLines(ctx, query)
	if err != nil {
		t.Fatalf("failed to get lines: %v", err)
	}

	expected := []string{"initial line 1", "initial line 2"}
	if len(lines) != len(expected) {
		t.Errorf("expected %d lines, got %d", len(expected), len(lines))
	}

	for i, expectedText := range expected {
		if i >= len(lines) {
			break
		}
		if lines[i].Text != expectedText {
			t.Errorf("line %d: expected %q, got %q", i, expectedText, lines[i].Text)
		}
		if lines[i].SessionID != sessionID {
			t.Errorf("line %d: expected session ID %q, got %q", i, sessionID, lines[i].SessionID)
		}
		if lines[i].Stream != "stdout" {
			t.Errorf("line %d: expected stream 'stdout', got %q", i, lines[i].Stream)
		}
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
		file.WriteString(`time=2024-01-01T00:00:00Z level=INFO msg=io stream=stdout line="test line"` + "\n")
		file.Close()
		defer os.Remove(tmpFile)

		reader, err := OpenTranscriptFile(tmpFile)
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

func TestNextLineAfter(t *testing.T) {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	// Create command with multiple lines
	cmd := exec.Command("sh", "-c", "echo line1; echo line2; echo line3")
	reader, err := StreamTranscript(ctx, cmd)
	if err != nil {
		t.Fatalf("failed to create stream transcript: %v", err)
	}
	defer reader.Close()

	// Read first line
	firstLine, err := reader.NextLine(ctx)
	if err != nil {
		t.Fatalf("failed to read first line: %v", err)
	}

	// Get line after the first one
	nextLine, err := reader.NextLineAfter(ctx, firstLine.Sequence)
	if err != nil && err != io.EOF {
		t.Fatalf("failed to read next line: %v", err)
	}

	if err != io.EOF && nextLine.Sequence <= firstLine.Sequence {
		t.Errorf("next line sequence %d should be > %d", nextLine.Sequence, firstLine.Sequence)
	}
}

func TestGetLines(t *testing.T) {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	// Create command with multiple lines
	cmd := exec.Command("sh", "-c", "echo line1; echo line2; echo line3")
	reader, err := StreamTranscript(ctx, cmd)
	if err != nil {
		t.Fatalf("failed to create stream transcript: %v", err)
	}
	defer reader.Close()

	// Small delay to let command produce output
	time.Sleep(100 * time.Millisecond)

	query := LineQuery{
		SessionID:     reader.SessionID(),
		AfterSequence: 0,
		Stream:        "all",
		Limit:         10,
		Follow:        false,
	}

	lines, err := reader.GetLines(ctx, query)
	if err != nil {
		t.Fatalf("failed to get lines: %v", err)
	}

	if len(lines) == 0 {
		t.Error("expected at least some lines")
	}

	// Verify sequence ordering
	for i := 1; i < len(lines); i++ {
		if lines[i].Sequence <= lines[i-1].Sequence {
			t.Errorf("line %d sequence %d should be > line %d sequence %d", i, lines[i].Sequence, i-1, lines[i-1].Sequence)
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
