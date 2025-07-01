package terminal

import (
	"bytes"
	"log/slog"
	"os"
	"strings"
	"testing"
)

func TestMemoryTranscript(t *testing.T) {
	transcript := NewMemoryTranscript()
	defer transcript.Close()

	// Write to different streams
	stdinWriter := transcript.StreamWriter("stdin")
	stdoutWriter := transcript.StreamWriter("stdout")
	stderrWriter := transcript.StreamWriter("stderr")

	stdinWriter.Write([]byte("input line 1\n"))
	stdoutWriter.Write([]byte("output line 1\n"))
	stderrWriter.Write([]byte("error line 1\n"))

	stdinWriter.Write([]byte("input line 2\n"))
	stdoutWriter.Write([]byte("output line 2\n"))

	// Check individual streams
	stdinData := transcript.GetStreamData("stdin")
	expectedStdin := "input line 1\ninput line 2\n"
	if string(stdinData) != expectedStdin {
		t.Errorf("expected stdin data %q, got %q", expectedStdin, string(stdinData))
	}

	stdoutData := transcript.GetStreamData("stdout")
	expectedStdout := "output line 1\noutput line 2\n"
	if string(stdoutData) != expectedStdout {
		t.Errorf("expected stdout data %q, got %q", expectedStdout, string(stdoutData))
	}

	stderrData := transcript.GetStreamData("stderr")
	expectedStderr := "error line 1\n"
	if string(stderrData) != expectedStderr {
		t.Errorf("expected stderr data %q, got %q", expectedStderr, string(stderrData))
	}

	// Check all streams
	allStreams := transcript.GetAllStreams()
	if len(allStreams) != 3 {
		t.Errorf("expected 3 streams, got %d", len(allStreams))
	}

	if string(allStreams["stdin"]) != expectedStdin {
		t.Errorf("expected stdin in all streams %q, got %q", expectedStdin, string(allStreams["stdin"]))
	}
}

func TestFileTranscript(t *testing.T) {
	tempFile := "/tmp/test-transcript.log"
	defer os.Remove(tempFile + "*") // Remove any generated files

	transcript, err := NewFileTranscript(tempFile)
	if err != nil {
		t.Fatalf("failed to create file transcript: %v", err)
	}
	defer transcript.Close()

	// Write to different streams
	stdoutWriter := transcript.StreamWriter("stdout")
	stderrWriter := transcript.StreamWriter("stderr")

	stdoutWriter.Write([]byte("test output line\n"))
	stderrWriter.Write([]byte("test error line\n"))

	// Close to flush buffers
	transcript.Close()

	// Check that file was created and contains data
	// Note: The actual filename will have a timestamp suffix
	files, err := os.ReadDir("/tmp")
	if err != nil {
		t.Fatalf("failed to read temp directory: %v", err)
	}

	found := false
	for _, file := range files {
		if strings.HasPrefix(file.Name(), "test-transcript-") && strings.HasSuffix(file.Name(), ".log") {
			found = true
			break
		}
	}

	if !found {
		t.Error("transcript file was not created")
	}
}

func TestLineWriter(t *testing.T) {
	buf := &bytes.Buffer{}
	logger := newTestLogger(buf)
	writer := newLineWriter("test-stream", logger)

	// Write complete lines
	writer.Write([]byte("line 1\n"))
	writer.Write([]byte("line 2\n"))

	// Write partial line
	writer.Write([]byte("partial"))
	writer.Write([]byte(" line"))
	writer.Write([]byte("\n"))

	// Close to flush remaining buffer
	writer.Close()

	output := buf.String()

	// Should contain logged lines
	if !strings.Contains(output, "line 1") {
		t.Errorf("expected output to contain 'line 1', got %q", output)
	}
	if !strings.Contains(output, "line 2") {
		t.Errorf("expected output to contain 'line 2', got %q", output)
	}
	if !strings.Contains(output, "partial line") {
		t.Errorf("expected output to contain 'partial line', got %q", output)
	}
	if !strings.Contains(output, "test-stream") {
		t.Errorf("expected output to contain stream name 'test-stream', got %q", output)
	}
}

func TestLineWriterPartialLines(t *testing.T) {
	buf := &bytes.Buffer{}
	logger := newTestLogger(buf)
	writer := newLineWriter("test", logger)

	// Write data without newlines
	writer.Write([]byte("partial"))
	writer.Write([]byte(" data"))

	// Should not have logged anything yet
	if buf.Len() > 0 {
		t.Error("expected no output for partial lines")
	}

	// Add newline to complete the line
	writer.Write([]byte(" complete\n"))

	// Now should have logged the complete line
	output := buf.String()
	if !strings.Contains(output, "partial data complete") {
		t.Errorf("expected output to contain complete line, got %q", output)
	}

	// Write some more partial data and close
	buf.Reset()
	writer.Write([]byte("final partial"))
	writer.Close()

	// Should log the final partial line on close
	output = buf.String()
	if !strings.Contains(output, "final partial") {
		t.Errorf("expected output to contain final partial line, got %q", output)
	}
}

func TestNoopTranscript(t *testing.T) {
	transcript := &NoopTranscript{}

	// Should not panic or error
	writer := transcript.StreamWriter("test")
	n, err := writer.Write([]byte("test data"))
	if err != nil {
		t.Errorf("unexpected error: %v", err)
	}
	if n != 9 {
		t.Errorf("expected 9 bytes written, got %d", n)
	}

	err = transcript.Close()
	if err != nil {
		t.Errorf("unexpected error on close: %v", err)
	}
}

// newTestLogger creates a simple text logger for testing
func newTestLogger(buf *bytes.Buffer) *slog.Logger {
	return slog.New(slog.NewTextHandler(buf, &slog.HandlerOptions{
		Level: slog.LevelDebug,
	}))
}
